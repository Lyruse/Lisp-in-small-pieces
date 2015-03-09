#lang racket
(require mzlib/compat) ;; to use atom? and getprop
(require compatibility/mlist)

(define (evaluate e r k)
  (if (atom? e)
      (cond [(symbol? e) (evaluate-variable e r k)]
            [else (evaluate-quote e r k)])
      (case (car e)
        [(quote) (evaluate-quote (cadr e) r k)]
        [(if) (evaluate-if (cadr e) (caddr e) (cadddr e) r k)]
        [(begin) (evaluate-begin (cdr e) r k)]
        [(set!) (evaluate-set! (cadr e) (caddr e) r k)]
        [(lambda) (evaluate-lambda (cadr e) (cddr e) r k)]
        [(catch) (evaluate-catch (cadr e) (cddr e) r k)]
        [(throw) (evaluate-throw (cadr e) (caddr e) r k)]
        [else (evaluate-application (car e) (cdr e) r k)])))
(define invoke
  (lambda (f v* r k)
    (cond
      [(primitive%? f)
       ((primitive%-address f) v* r k)]
      [(continuation%? f)
       (if (= 1 (length v*))
           (resume f (car v*))
           (error "Continuation expect one argument" v* r k))]
      [else (let ([env (extend-env (function%-env f)
                                   (function%-vars f)
                                   v*)])
              (evaluate-begin (function%-body f) env k))])))
(define resume
  (lambda (k v)
    (cond
      [(if-cont%? k)
       (evaluate (if v (if-cont%-et k) (if-cont%-ef k)) 
                 (if-cont%-r k)
                 (continuation%-k k))]
      [(begin-cont%? k)
       (evaluate-begin (cdr (begin-cont%-e* k))
                       (begin-cont%-r k)
                       (continuation%-k k))]
      [(set!-cont%? k)
       (update! (set!-cont%-r k) (set!-cont%-n k) (continuation%-k k) v)]
      [(evfun-cont%? k)
       (evaluate-arguments (evfun-cont%-e* k)
                           (evfun-cont%-r k)
                           (apply-cont% (continuation%-k k)
                                        v
                                        (evfun-cont%-r k)))]
      [(argument-cont%? k)
       (evaluate-arguments (cdr (argument-cont%-e* k))
                           (argument-cont%-r k)
                           (gather-cont% (continuation%-k k) v))]
      [(gather-cont%? k)
       (resume (continuation%-k k)
               (cons (gather-cont%-v k) v))]
      [(catch-cont%? k)
       (evaluate-begin (catch-cont%-body k)
                       (catch-cont%-r k)
                       (labeled-cont% (continuation%-k k) v))]
      [(throwing-cont%? k)
       (resume (throwing-cont%-cont k) v)]
      [(apply-cont%? k)
       (invoke (apply-cont%-f k)
               v
               (apply-cont%-r k)
               (continuation%-k k))]
      [(bottom-cont%? k)
       ((bottom-cont%-f k) v)]
      [(throw-cont%? k)
       (catch-lookup k v k)]
      [(labeled-cont%? k)
       (resume (continuation%-k k) v)])))
(define catch-lookup
  (lambda (k tag kk)
    (match k
      [(bottom-cont% c f)
       (error "No associated catch" k tag kk)]
      [x #:when (labeled-cont%? x)
         (if (eqv? tag (labeled-cont%-tag k))
             (evaluate (throw-cont%-form kk)
                       (throw-cont%-r kk)
                       (throwing-cont% kk tag k))
             (catch-lookup (continuation%-k k) tag kk))]
      [(continuation% c)
       (catch-lookup c tag kk)]
      [else (error "Not a continuation" k tag kk)])))
(define lookup
  (lambda (r n k)
    (cond
      [(null-env%? r)
       (error "Unknown variable:" n r k)]
      [(variable-env%? r)
       (if (eqv? n (full-env%-name r))
           (resume k (variable-env%-value r))
           (lookup (full-env%-others r) n k))]
      [(full-env%? r)        ;; if this clause come first, it would be wrong.
       (lookup (full-env%-others r) n k)])))
(define update!
  (lambda (r n k v)
    (cond
      [(null-env%? r)
       (error "Unknown variable" n r k)]
      [(variable-env%? r)
       (if (eqv? n (full-env%-name r))
           (begin (set-variable-env%-value! r v)
                  (resume k v))
           (update! (full-env%-others r) n k v))]
      [(full-env%? r)
       (update! (full-env%-others r) n k v)])))
(define (extend-env env names values)
  (cond [(and (pair? names) (pair? values))
         (variable-env%
          (extend-env env (cdr names) (cdr values))
          (car names)
          (car values))]
        [(and (null? names) (null? values)) env]
        [(symbol? names)
         (variable-env% env names values)]
        [else (error "Arity mismatch")]))

;; classes for continuation and environment
(struct value% () #:transparent)
(struct function% value% (vars body env) #:transparent)
(struct primitive% value% (name address) #:transparent)

(struct environment% () #:transparent)
(struct null-env% environment% () #:transparent)
(struct full-env% environment% (others name) #:transparent)
(struct variable-env% full-env% ((value #:mutable)) #:transparent)

(struct continuation% (k) #:transparent)
(struct bottom-cont% continuation% (f) #:transparent)
(struct if-cont% continuation% (et ef r) #:transparent)
(struct begin-cont% continuation% (e* r) #:transparent)
(struct set!-cont% continuation% (n r) #:transparent)
(struct evfun-cont% continuation% (e* r) #:transparent)
(struct apply-cont% continuation% (f r) #:transparent)
(struct argument-cont% continuation% (e* r) #:transparent)
(struct gather-cont% continuation% (v) #:transparent)
(struct catch-cont% continuation% (body r) #:transparent)
(struct labeled-cont% continuation% (tag) #:transparent)
(struct throw-cont% continuation% (form r) #:transparent)
(struct throwing-cont% continuation% (tag cont) #:transparent)

;; multiple functions for evaluate the different forms
(define evaluate-quote
  (lambda (v r k)
    (resume k v)))
(define evaluate-if
  (lambda (ec et ef r k)
    (evaluate ec r (if-cont% k et ef r))))
(define (evaluate-begin e* r k)
  (match e*
    [`(,a . ,b)
     (if (pair? b)
         (evaluate a r (begin-cont% k e* r))
         (evaluate a r k))]
    [else (resume k empty-begin-value)]))
(define empty-begin-value (cons 'empty 'begin))
(define (evaluate-variable n r k)
  (lookup r n k))
(define (evaluate-set! n e r k)
  (evaluate e r (set!-cont% k n r)))
(define (evaluate-lambda n* e* r k)
  (resume k (function% n* e* r)))
(define (evaluate-application e e* r k)
  (evaluate e r (evfun-cont% k e* r)))
(define (evaluate-arguments e* r k)
  (if (pair? e*)
      (evaluate (car e*) r (argument-cont% k e* r))
      (resume k '())))
(define (evaluate-catch tag body r k)
  (evaluate tag r (catch-cont% k body r)))
(define (evaluate-throw tag form r k)
  (evaluate tag r (throw-cont% k form r)))


(define-syntax definitial
  (syntax-rules ()
    [(_ name)
     (definitial name 'void)]
    [(_ name value)
     (begin (set! r.init (variable-env% r.init 'name value))
            'name)]))
(define-syntax defprimitive
  (syntax-rules ()
    [(_ name value arity)
     (definitial name
       (primitive%
        'name
        (lambda (v* r k)
          (if (= arity (length v*))
              (resume k (apply value v*))
              (error "Incorrect arity" 'name v*)))))]))
(define r.init (null-env%))
(defprimitive cons cons 2)
(defprimitive car car 1)
(defprimitive + + 2)
(defprimitive - - 2)
(defprimitive * * 2)
(defprimitive = = 2)
(definitial call/cc
  (primitive%
   'call/cc
   (lambda (v* r k)
     (if (= 1 (length v*))
         (invoke (car v*) (list k) r k)
         (error "Incorrect arity" 'call/cc v*)))))



;; then we can run it
(define (chapter3-interpreter)
  (define (toplevel)
    (evaluate (read)
              r.init
              (bottom-cont% 'void (lambda (x) (display x) (newline))))
    (toplevel))
  (toplevel))

;; test
#;
(((lambda (f)
    ((lambda (mk) (mk mk))
     (lambda (mk)
       (f (lambda (x) ((mk mk) x))))))
   (lambda (f)
     (lambda (n)
       (if (= n 0)
           1
           (* n (f (- n 1)))))))
   5)
#;
(evaluate '(catch 2 (* 7 (catch 1 
                           (* 3 (catch 2
                                 (throw 1 (throw 2 5)))))))
              r.init
              (bottom-cont% 'void (lambda (x) (display x) (newline))))
;; =>105
#;
(evaluate '(catch 2 (* 7 (throw 1 
                           (throw 2
                             3))))
              r.init
              (bottom-cont% 'void (lambda (x) (display x) (newline))))

(evaluate '(catch 2 (* 7 (throw 2
                                (begin 55 (+ 6 7)))))
              r.init
              (bottom-cont% 'void (lambda (x) (display x) (newline))))
#;
(evaluate '((catch 2 (lambda (x)
                      (* x (throw 2  ;; not work! No assosiated match.
                                5))))
            10)
              r.init
              (bottom-cont% 'void (lambda (x) (display x) (newline))))

(evaluate '((catch 2 (lambda (x)
                       (set! x 100)
                       (+ x x)))
            10)
              r.init
              (bottom-cont% 'void (lambda (x) (display x) (newline))))
