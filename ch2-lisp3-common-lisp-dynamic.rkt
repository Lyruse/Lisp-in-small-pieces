#lang racket

;; Date: 2015-03-03
;; Author: Lyruse Huang
;; About Lisp3: separate var world and function world, dynamic vars
;; and to improve the way function calls were handled 

;; display-cyclic-spine is a good example about cyclic list data

(require mzlib/compat) ;; to use atom? and getprop
(require compatibility/mlist)
(provide (rename-out [test cl-dynamic-test]))


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

(define invoke   ;; no longer used in this version of lisp
  (lambda (fn args denv)
    (if (procedure? fn)  ;; use the definition language's closure
        (fn args denv)
        (error "Not a function: " fn))))
(define make-function
  (lambda (vars body env fenv) ;; lexical binding
    (lambda (values denv)
      (eprogn body (extend env vars values) fenv denv))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;add some global environment utilities;;;;;;;;;;;;;;;;
(define env.global env.init)
(define fenv.global '())
(define-syntax definitial-function
  (syntax-rules ()
    [(_ name)
     (begin (set! fenv.global (mcons (mcons 'name 'void) fenv.global))
            (void))]
    [(_ name value)
     (begin (set! fenv.global (mcons (mcons 'name value) fenv.global)))]))
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
     (definitial-function name
       (lambda (values denv)
         (if (= arity (length values))
             (apply value values)
             (error "Incorrect arity " (list 'name values)))))]))


(define eprogn
  (lambda (exps env fenv denv)
    (if (pair? exps)
        (if (pair? (cdr exps))
            (begin (evaluate (car exps) env fenv denv)
                   (eprogn (cdr exps) env fenv denv))
            (evaluate (car exps) env fenv denv))
        empty-begin)))
(define empty-begin 813)

(define evlis
  (lambda (exps env fenv denv)
    (if (pair? exps)
        (cons (evaluate (car exps) env fenv denv)
              (evlis (cdr exps) env fenv denv))
        '())))
(define (evaluate e env fenv denv)
  (if (atom? e)
      (cond
        [(symbol? e) 
         (cl.lookup e env denv)]
        [(or (number? e) (string? e)
             (char? e) (boolean? e))e]
        [else (error "Can't evaluate " e)])
      (case (car e)
        [(quote) (cadr e)]
        [(if) (if (evaluate (cadr e) env fenv denv)
                  (evaluate (caddr e) env fenv denv)
                  (evaluate (cadddr e) env fenv denv))]
        [(function)
         (cond [(symbol? (cadr e))
                (f.lookup (cadr e) fenv)]
               [(and (pair? (cadr e)) (eq? (car (cadr e)) 'lambda))
                (make-function
                 (cadr (cadr e)) (cddr (cadr e)) env fenv)]
               [else (error "Incorrect function " (cadr e))])]
        [(begin) (eprogn (cdr e) env fenv denv)]
        [(set!) (update! (cadr e) env (evaluate (caddr e) env fenv denv))]
        [(lambda) (make-function (cadr e) (cddr e) env fenv)]
        [(let) (eprogn (cddr e)
                       (extend env (map car (cadr e))
                               (map (lambda (e) (evaluate e env fenv denv)) 
                                    (map cadr (cadr e))))
                       fenv
                       denv)]
        [(dynamic) (lookup (cadr e) denv)]
        [(dynamic-set!)
         (update! (cadr e)
                  denv
                  (evaluate (caddr e) env fenv denv))]
        [(dynamic-let)
         (eprogn (cddr e)
                 (special-extend env (map car (cadr e)))
                 fenv
                 (extend denv
                         (map car (cadr e))
                         (map (lambda (e)
                                (evaluate e env fenv denv))
                              (map cadr (cadr e)))))]
        [else (evaluate.app (car e)
                      (evlis (cdr e) env fenv denv)
                      env
                      fenv
                      denv)])))
(define f.lookup
  (lambda (id env)
    (if (mpair? env)
        (if (eq? (mcaar env) id)
            (mcdar env)
            (f.lookup id (mcdr env)))
        (lambda (values denv) ;; returns a function when not found the corresponding fun
          (error "No such functional binding" id)))))

(define cl.lookup
  (lambda (var env denv)
    (let look ([env env])
      (if (mpair? env)
          (if (mpair? (mcar env))
              (if (eq? (mcaar env) var)
                  (mcdar env)
                  (look (cdr env)))
              (if (eq? (mcar env) var)
                  ;;lookup in the current dynamic env
                  (let lookup-in-denv ([denv denv])
                    (if (mpair? denv)
                        (if (eq? (mcaar denv) var)
                            (mcdar denv)
                            (lookup-in-denv (mcdr denv)))
                        (lookup var env.global)))
                  (look (mcdr env))))
          (error "No such binding" var)))))
(define (special-extend env vars)
  (mappend (list->mlist vars) env))
(define evaluate.app
  (lambda (fn args env fenv denv)
    (cond
      [(symbol? fn)
       ((f.lookup fn fenv) args denv)]     
      [(and (pair? fn) (eq? (car fn) 'lambda))
       (eprogn (cddr fn)
               (extend env (cadr fn) args)
               fenv
               denv)]
      [else (error "Incorrect functional term " fn)])))


;;; add some global variables and function
(defprimitive cons cons 2)
(defprimitive car car 1)
(defprimitive + + 2)
(defprimitive eq? eq? 2)
(defprimitive * * 2)
(defprimitive - - 2)
(definitial-function list (lambda (id) id))  ;; Exercise 1.6
(definitial-function funcall
  (lambda (args denv)
    (if (> (length args) 1)
        ((car args) (cdr args) denv)
        (error "Incorrect arity ~a" 'funcall))))

;; for testing
(define (Lisp2)
  (define (toplevel)
    (display (evaluate (read) env.global fenv.global))
    (toplevel))
  (toplevel))
(define (test exp)
  (evaluate exp env.global fenv.global env.init))

#;
(test '(dynamic-let ([x 2])                     
                    (+ x                     ;dynamic
                       (let ([x (+           ;lexical
                                 x x)])      ;dynamic
                         (+ x                ;lexical
                            (dynamic x)))))) ;dynamic
; ==>8