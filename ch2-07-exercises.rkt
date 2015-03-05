#lang racket

;; 2015-03-05
;; 
;; Notice NfixN which is function that receive a list of functions and return 
;; a list of fixed point of the functions
;; because I don't develop it from small to big,
;; the process is difficult.



(require "ch2-lisp2.rkt") ;; gets lisp2-test
(require "ch2-lisp3-common-lisp-dynamic.rkt") ;; gets cl-dynamic-test

;; Exercise 2.1
;; translate the exp below to Scheme
#;(funcall (funtion funcall) (function funcall) (function cons) 1 2)
#;(cons 1 2)
;; funcall is just a function stored inside function environment,
;; when called, it's applied to 
#;((funtion funcall) (function funcall) (function cons) 1 2) 
;; then the result is the result of 
;; invoking funcall on ((function funcall) (function cons) 1 2)) as arguments
;; then again invoke funcall on ((function cons) 1 2),
;; then comes the final real operation that cons on 1 and 2, 
;; the result is (1 . 2).


;; Exercise 2.3
;; add number and list inside the function position to make it special handled
;; inside invoke evaluation.

;; change the invoke(apply) to handle function as number and list
(define (spe.invoke fn args)
  (cond
    [(procedure? fn)
     (fn args)]
    [(number? fn)
     (if (= (length args) 1)
         (if (>= fn 0)  ;; here 0 get the car of list and 1 gets cadr.
             (list-ref (car args) fn)  
             (list-tail (car args) (- fn)))
         (error "Incorrect arity" fn))]
    [(pair? fn)
     (map (lambda (f) (apply f args)) fn)]
    [else (error "Can't apply" fn)]))



(require "ch2-04-lisp-bind-de.rkt") ;; gets set-assoc/de! and cl-de-test
;; Exercise 2.4
;; change the assoc/de to receive one more argument as comparer
;; such as eq? or equal?.
#;
(set-assoc/de!   ;;; this doesn't work
 (lambda (values current.denv)
    (match values
      [`(,tag ,compare ,def)
       (let look ([denv current.denv])
         (match denv
           [(mcons a d)
            (if (compare `(,tag ,(mcar a)) denv)  ;; this must be (values denv) form
                (mcdr a)
                (look d))]
           [else (invoke def (list tag) current.denv)]))]
      [else (error "incorrect arity" 'assoc/de)])))
#;
(cl-de-test '(bind/de 'x 100
                        (lambda ()
                          (let ([x 1])
                            (+ x (assoc/de1'x eq? error))))))
;; =>101

;; ch2-04-lisp-bind-de.rkt:70:18: set!:
;; cannot mutate module-required identifier in: env.global
;; but the code below works
;> (get-x)
;100
;> (set-x! 200)
;> (get-x)
;200

;; Exercise 2.5
;; write macro to simulate the special form dynamic-let, dynamic, and dynamic-set!
(define-syntax dynamic-let
  (syntax-rules ()
    [(_ () body ...)
     (begin body ...)]
    [(_ ([var val] [vars vals] ...) body ...)  ;;[vars vals] ... can be replaced 
     (bind/de 'var val                         ;; with a single others ...
              (lambda ()
               (dynamic-let ([vars vals] ...) body ...)))]))

(define-syntax dynamic
  (syntax-rules ()
    [(_ var)
     (assoc/de 'var error)]))
(define-syntax dynamic-set!
  (syntax-rules ()
    [(_ var value)  ;; only if the value stored in denv can be set-car!
     (set-car! (assoc/de 'var error) value)]));; use the set-car! to change the car value

;; Exercise 2.6
;; (begin (putprop 'symbol 'key 'value)
;;        (getprop 'symbol 'key)) => value
(define table (make-hash))
(define getprop
  (lambda (sym key)
    (let ([al (hash-ref table sym (lambda () #f))])
      (if al
          (let ([rt (assq key al)])
            (if rt
                (unbox (cdr rt))
                #f))
          #f))))
(define putprop
  (lambda (sym key value)
    (let ([al (hash-ref table sym (lambda () '()))])
      (let ([rt (assq key al)])
        (if rt
            (set-box! (cdr rt) value)
            (hash-set! table sym (cons (cons key (box value)) al)))))))

;; Exercise 2.7 and 2.8 already done in lisp2

;; Exercise 2.10
;; write a fixN that suport any arguments that the fixed point accept
(define fix
  (lambda (f)
    ((lambda (mk) (mk mk))
     (lambda (mk)
       (f (lambda args (apply (mk mk) args)))))))
#;
(fix (lambda (f)
       (lambda ls
         (if (= 0 (car ls))
             (expt 2 (cdr ls))
             (f (cons (- (car ls) 1) (f 0 (cdr ls))))))))
#;
((fix (lambda (f)
       (lambda ls
         (if (= 0 (car ls))
             (expt 2 (cadr ls))
             (f (- (car ls) 1) (f 0 (cadr ls)))))))
   1 10)

;; Exercise 2.12
(define odd? #f)
(define even? #f)
(define NfixN ;; don't forget to develop it from small to big!!!!
  (lambda (ls)
    ((lambda (mk) (mk mk))
     (lambda (mk)
       (map
        (lambda (f) (apply f (map (lambda (i)
                                    (lambda a (apply 
                                               (list-ref (mk mk) i)
                                               a)))
                                  (stream->list (in-range (length ls))))))
        ls)))))
#;
(let ([odd-and-even
       (NfixN (list (lambda (odd? even?)
                      (lambda (n)
                        (if (= n 0) #t (odd? (- n 1)))))
                    (lambda (odd? even?)
                      (lambda (n)
                        (if (= n 0) #f (even? (- n 1)))))))])
  (set! even? (car odd-and-even))
  (set! odd? (cadr odd-and-even))
  (odd? 0))

;; Exercise 1.12
;; klop has just a couple more w in the (w w) form
(define klop
  (let ([r (lambda (s c h e m e_)
             (lambda (f)
               (f (lambda (n)
                    (((h e m e_ h c s) f) n)))))])
    (r r r r r r r)))
(define metafact
  (lambda (f)
    (lambda (n)
      (if (= n 0)
          1
          (* n (f (- n 1)))))))
((klop metafact) 5)
  