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
            (let ([value (mcdar env)])
              (if (eq? value the-uninitialized-marker)
                  (error "Unitialized binding" id)
                  value))
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
  (lambda (fn args )
    (if (procedure? fn)  ;; use the definition language's closure
        (fn args )
        (error "Not a function: " fn))))
(define make-function
  (lambda (vars body env) ;; lexical binding
    (lambda (values )
      (eprogn body (extend env vars values) ))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;add some global environment utilities;;;;;;;;;;;;;;;;
(define env.global env.init)

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
       (lambda (values )
         (if (= arity (length values))
             (apply value values)
             (error "Incorrect arity " (list 'name values)))))]))


(define eprogn
  (lambda (exps env )
    (if (pair? exps)
        (if (pair? (cdr exps))
            (begin (evaluate (car exps) env )
                   (eprogn (cdr exps) env ))
            (evaluate (car exps) env ))
        empty-begin)))
(define empty-begin 813)

(define evlis
  (lambda (exps env )
    (if (pair? exps)
        (cons (evaluate (car exps) env )
              (evlis (cdr exps) env ))
        '())))
(define (evaluate e env )
  (if (atom? e)
      (cond
        [(symbol? e) 
         (lookup e env)]
        [(or (number? e) (string? e)
             (char? e) (boolean? e))e]
        [else (error "Can't evaluate " e)])
      (case (car e)
        [(quote) (cadr e)]
        [(if) (if (evaluate (cadr e) env )
                  (evaluate (caddr e) env )
                  (evaluate (cadddr e) env ))]        
        [(begin) (eprogn (cdr e) env )]
        [(set!) (update! (cadr e) env (evaluate (caddr e) env ))]
        [(lambda) (make-function (cadr e) (cddr e) env)]
        [(let) (eprogn (cddr e)
                       (extend env (map 
                                    (lambda (binding)
                                      (if (symbol? binding)
                                          binding
                                          (car binding)))
                                    (cadr e))
                               (map (lambda (binding) 
                                      (if (symbol? binding)
                                          the-uninitialized-marker
                                          (evaluate (cadr binding) env )))
                                    (cadr e)))
                       )]
        [else (invoke (evaluate (car e) env )
                      (evlis (cdr e) env )
                      )])))


(define the-uninitialized-marker (cons 'non 'initialized))
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
  (lambda (args )
    (if (> (length args) 1)
        (invoke (car args) (cdr args) )
        (error "Incorrect arity ~a" 'funcall))))

(definitial error
  (lambda (args )
    (if (= (length args) 1)
        (error "The tag is not bound" (car args))
        (error "Incorrect arity ~a" 'error))))


;; for testing
(define (Lisp)
  (define (toplevel)
    (display (evaluate (read) env.global ))
    (toplevel))
  (toplevel))
(define (test exp)
  (evaluate exp env.global))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; tests for letrec:
;> (test '(let (even? odd?)
;           (let ([temp1 (lambda (n) (if (= n 0) #t (odd? (- n 1))))]
;                 [temp2 (lambda (n) (if (= n 0) #f (even? (- n 1))))])
;             (set! even? temp1)
;             (set! odd? temp2)
;             (even? 4))))
;=> true
