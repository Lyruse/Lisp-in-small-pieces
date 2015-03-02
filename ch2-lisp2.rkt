#lang racket

;; Date: 2015-03-02
;; Author: Lyruse Huang
;; 
;;
(require mzlib/compat) ;; to use atom? and getprop



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
  (lambda (fn args)
    (if (procedure? fn)  ;; use the definition language's closure
        (fn args)
        (error "Not a function: " fn))))
(define make-function
  (lambda (vars body env fenv) ;; lexical binding
    (lambda (values)
      (eprogn body (extend env vars values) fenv))))


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
       (lambda (values)
         (if (= arity (length values))
             (apply value values)
             (error "Incorrect arity " (list 'name values)))))]))


(define eprogn
  (lambda (exps env fenv)
    (if (pair? exps)
        (if (pair? (cdr exps))
            (begin (evaluate (car exps) env fenv)
                   (eprogn (cdr exps) env fenv))
            (evaluate (car exps) env fenv))
        empty-begin)))
(define empty-begin 813)

(define evlis
  (lambda (exps env fenv)
    (if (pair? exps)
        (cons (evaluate (car exps) env fenv)
              (evlis (cdr exps) env fenv))
        '())))
(define (evaluate e env fenv)
  (if (atom? e)
      (cond
        [(symbol? e) 
         (lookup e env)]
        [(or (number? e) (string? e)
             (char? e) (boolean? e))e]
        [else (error "Can't evaluate " e)])
      (case (car e)
        [(quote) (cadr e)]
        [(if) (if (evaluate (cadr e) env fenv)
                  (evaluate (caddr e) env fenv)
                  (evaluate (cadddr e) env fenv))]
        [(function)
         (if (symbol? (cadr e))
             (lookup (cadr e) fenv)
             (error "Incorrect function " (cadr e)))]
        [(begin) (eprogn (cdr e) env fenv)]
        [(set!) (update! (cadr e) env (evaluate (caddr e) env fenv))]
        [(lambda) (make-function (cadr e) (cddr e) env fenv)]
        [(flet)
         (eprogn
          (cddr e)
          env
          (extend fenv
                  (map car (cadr e))
                  (map (lambda (def)
                         (make-function (cadr def) (cddr def) env fenv))
                       (cadr e))))]
        [else (evaluate.app (car e)
                      (evlis (cdr e) env fenv)
                      env
                      fenv)])))
(define evaluate.app
  (lambda (fn args env fenv)
    (cond
      [(symbol? fn)
       (invoke (lookup fn fenv) args)]
      #;
      [(number? fn)  ;; not a good innovation
       (cond
         [(= 1 fn)
          (car (car args))]
         [(= -1 fn)
          (cdr (car args))]
         [(> fn 0)
          (evaluate.app (- fn 1) (list (cdr (car args))) env fenv)]
         [else (evaluate.app (+ fn 1) (list (cdr (car args))) env fenv)])]
      [(and (pair? fn) (eq? (car fn) 'lambda))
       (eprogn (cddr fn)
               (extend env (cadr fn) args)
               fenv)]
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
  (lambda (args)
    (if (> (length args) 1)
        (invoke (car args) (cdr args))
        (error "Incorrect arity ~a" 'funcall))))

;; for testing
(define (Lisp2)
  (define (toplevel)
    (display (evaluate (read) env.global fenv.global))
    (toplevel))
  (toplevel))
(define (test exp)
  (evaluate exp env.global fenv.global))

#;(funcall
   ((lambda (f)
     ((lambda (mk)
       (funcall f (lambda (x) (funcall (funcall mk mk) x))))
      (lambda (mk)
        (funcall f (lambda (x) (funcall (funcall mk mk) x))))))
   (lambda (f)
     (lambda (n)
       (if (eq? 0 n)
           1
           (funcall (function *) n (funcall f (- n 1)))))))
   5)
;==> 120
