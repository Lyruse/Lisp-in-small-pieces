#lang racket

;; Date: 2015-02-28
;; Author: Lyruse Huang

(define atom?
  (lambda (exp)
    (not (pair? exp))))

(define eprogn
  (lambda (exps env)
    (if (pair? exps)
        (if (pair? (cdr exps))
            (begin (evaluate (car exps) env)
                   (eprogn (cdr exps) env))
            (evaluate (car exps) env))
        empty-begin)))
(define empty-begin 813)

(define evlis
  (lambda (exps env)
    (if (pair? exps)
        (cons (evaluate (car exps) env)
              (evlis (cdr exps) env))
        '())))
(define mcaar (lambda (ls) (mcar (mcar ls))))
(define mcdar (lambda (ls) (mcdr (mcar ls))))
(define env.init '())
(define extend
  (lambda (env var value)
    (cond
      [(pair? var)
       (if (pair? value)
           (mcons (mcons (car var) (car value))
                  (extend env (cdr var) (cdr value)))
           (error "Too less values"))]
      [(null? var)
       (if (null? value)
           env
           (error "Too much values"))]
      [(symbol? var) (mcons (mcons var value) env)])))
; Symbol Environment -> value
(define lookup
  (lambda (id env)
    (if (mpair? env)
        (if (eq?  (mcaar env) id)
            (mcdar env)
            (lookup id (mcdr env)))
        (error "No such binding for ~s" id))))
(define update!
  (lambda (id env value)
    (if (mpair? env)
        (if (eq? (mcaar env) id)
            (begin (set-mcdr! (mcar env) value)
                   value)
            (update! id (mcdr env) value))
        (error "No such biding for ~s" id))))

(define invoke
  (lambda (fn args)
    (if (procedure? fn)  ;; use the definition language's closure
        (fn args)
        (error "Not a function: ~s" fn))))
(define make-function
  (lambda (vars body env) ;; lexical binding
    (lambda (values)
      (eprogn body (extend env vars values)))))

(define (evaluate e env)
  (if (atom? e)
      (cond
        [(symbol? e) 
         (lookup e env)]
        [(or (number? e) (string? e)
             (char? e) (boolean? e))e]
        [else (error "Can't evaluate ~s" e)])
      (case (car e)
        [(quote) (cadr e)]
        [(if) (if (evaluate (cadr e) env)
                  (evaluate (caddr e) env)
                  (evaluate (cadddr e) env))]
        [(begin) (eprogn (cdr e) env)]
        [(set!) (update! (cadr e) env (evaluate (caddr e) env))]
        [(lambda) (make-function (cadr e) (cddr e) env)]
        [else (invoke (evaluate (car e) env)
                      (evlis (cdr e) env))])))
