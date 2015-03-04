#lang racket

;; Date: 2015-03-03
;; Author: Lyruse Huang
;; About Lisp3: separate var world and function world, dynamic vars
;; and to improve the way function calls were handled 

;; display-cyclic-spine is a good example about cyclic list data

(require mzlib/compat) ;; to use atom? and getprop
(require compatibility/mlist)


(define mcaar (lambda (ls) (mcar (mcar ls))))
(define mcdar (lambda (ls) (mcdr (mcar ls))))
(define env.init '())
(define extend
  (lambda (env vars values)
    (cond
      [(pair? vars)
       (if (pair? values)
           (mcons (mcons (car vars) (car values))
                  (extend env (cdr vars) (cdr values)))
           (error "Too less values"))]
      [(null? vars)
       (if (null? values)
           env
           (error "Too much values"))]
      [(symbol? vars) (mcons (mcons vars values) env)])))
; Symbol Environment -> value
(define lookup
  (lambda (id env)
    (if (mpair? env)
        (if (eq?  (mcaar env) id)
            (mcdar env)
            (lookup id (mcdr env)))
        (error "No such binding for " id))))
(define update!
  (lambda (id env value)
    (if (mpair? env)
        (if (eq? (mcaar env) id)
            (begin (set-mcdr! (mcar env) value)
                   value)
            (update! id (mcdr env) value))
        (error "No such biding for " id))))

(define invoke
  (lambda (fn args denv)
    (if (procedure? fn)  ;; use the definition language's closure
        (fn args denv)
        (error "Not a function: " fn))))
(define make-function
  (lambda (vars body env) ;; lexical binding
    (lambda (values denv)
      (eprogn body (extend env vars values) denv))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;add some global environment utilities;;;;;;;;;;;;;;;;
(define env.global env.init)
(define denv.global '())

(define-syntax definitial
  (syntax-rules ()
    [(_ name)
     (begin (set! env.global (mcons (mcons 'name 'void) env.global))
            (void))]
    [(_ name value)
     (begin (set! env.global (mcons (mcons 'name value) env.global)))]))
(define-syntax defprimitive
  (syntax-rules ()
    [(_ name value arity)
     (definitial name
       (lambda (values denv)
         (if (= arity (length values))
             (apply value values)
             (error "Incorrect arity " (list 'name values)))))]))


(define eprogn
  (lambda (exps env denv)
    (if (pair? exps)
        (if (pair? (cdr exps))
            (begin (evaluate (car exps) env denv)
                   (eprogn (cdr exps) env denv))
            (evaluate (car exps) env denv))
        empty-begin)))
(define empty-begin 813)

(define evlis
  (lambda (exps env denv)
    (if (pair? exps)
        (cons (evaluate (car exps) env denv)
              (evlis (cdr exps) env denv))
        '())))
(define (evaluate e env denv)
  (if (atom? e)
      (cond
        [(symbol? e) 
         (lookup e env)]
        [(or (number? e) (string? e)
             (char? e) (boolean? e))e]
        [else (error "Can't evaluate " e)])
      (case (car e)
        [(quote) (cadr e)]
        [(if) (if (evaluate (cadr e) env denv)
                  (evaluate (caddr e) env denv)
                  (evaluate (cadddr e) env denv))]        
        [(begin) (eprogn (cdr e) env denv)]
        [(set!) (update! (cadr e) env (evaluate (caddr e) env denv))]
        [(lambda) (make-function (cadr e) (cddr e) env)]
        [(let) (eprogn (cddr e)
                       (extend env (map car (cadr e))
                               (map (lambda (e) (evaluate e env denv)) (map cadr (cadr e))))
                       denv)]
        [(dynamic) (lookup (cadr e) denv)]
        [(dynamic-set!)
         (update! (cadr e)
                  denv
                  (evaluate (caddr e) env denv))]
        [(dynamic-let)
         (eprogn (cddr e)
                 env
                 (extend denv
                         (map car (cadr e))
                         (map (lambda (e)
                                (evaluate e env denv))
                              (map cadr (cadr e)))))]
        [else (invoke (evaluate (car e) env denv)
                      (evlis (cdr e) env denv)
                      denv)])))



;;; add some global variables and function
(defprimitive cons cons 2)
(defprimitive car car 1)
(defprimitive + + 2)
(defprimitive eq? eq? 2)
(defprimitive * * 2)
(defprimitive - - 2)
(defprimitive = = 2)
(definitial list (lambda (id) id))  ;; Exercise 1.6
(definitial funcall
  (lambda (args denv)
    (if (> (length args) 1)
        (invoke (car args) (cdr args) denv)
        (error "Incorrect arity ~a" 'funcall))))

(definitial error
  (lambda (args denv)
    (if (= (length args) 1)
        (error "The tag is not bound" (car args))
        (error "Incorrect arity ~a" 'error))))
(definitial bind/de
  (lambda (values denv)
    (match values
      [`(,tag ,value ,thunk)
       (invoke thunk '() (extend denv (list tag) (list value)))]
      [else (error "incoreect arity" 'bind/de)])))
(definitial assoc/de
  (lambda (values current.denv)
    (match values
      [`(,tag ,def)
       (let look ([denv current.denv])
         (match denv
           [(mcons a d)
            (if (eqv? tag (mcar a))
                (mcdr a)
                (look d))]
           [else (invoke def (list tag) current.denv)]))]
      [else (error "incorrect arity" 'assoc/de)])))

;; for testing
(define (Lisp)
  (define (toplevel)
    (display (evaluate (read) env.global denv.global))
    (toplevel))
  (toplevel))
(define (test exp)
  (evaluate exp env.global denv.global))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; tests for bind/de
;> (test '(bind/de 'x 2
;                  (lambda ()
;                    (+ (assoc/de 'x error)
;                       (let ([x (+ (assoc/de 'x error) (assoc/de 'x error))])
;                         (+ x (assoc/de 'x error)))))))
;=> 8
#;
(test '(bind/de 'x 100
                (lambda ()
                  ((bind/de 'x 2
                            (lambda ()
                              (lambda ()
                                (+ (assoc/de 'x error)
                                   (let ([x (+ (assoc/de 'x error) (assoc/de 'x error))])
                                     (+ x (assoc/de 'x (lambda () 5))))))))))))
;; =>400