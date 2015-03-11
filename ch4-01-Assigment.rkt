#lang racket

; date: 2015-03-12
(require mzlib/compat) ;; to use atom? and getprop
(require compatibility/mlist)
(provide (all-defined-out))

;; the real things begins here
;---------------------------------------------------------------------------
;; environments and memory utilities
; env
(define (r.init id)
  (error "No binding for" id))
(define (update s a v) ;; can also used to extend env
  (lambda (aa)
    (if (eqv? a aa) v (s aa)))) ;; the newer value comes first.
(define (update* s a* v*)
  ;; assume (= (length a*) (length v*))
  (if (pair? a*)
      (update* (update s (car a*) (car v*)) (cdr a*) (cdr v*))
      s))

(define (allocate n s q)
  (if (> n 0)
      (let ([a (new-location s)])
        (allocate (- n 1)
                  (expand-store a s)
                  (lambda (a* ss)
                    (q (cons a a*) ss))))
      (q '() s)))
(define (expand-store high-location s)
  (update s 0 high-location))
(define (new-location s)
  (+ 1 (s 0)))

(define s.init
  (expand-store 0 (lambda (a) (error "No such address" a))))


;; the main interpreter
(define (evaluate e r s k)
  (match e
    [`,x #:when (atom? x)
         (if (symbol? x) 
             (evaluate-variable e r s k)
             (evaluate-quote e r s k))]
    [`(quote ,e)
     (evaluate-quote e r s k)]
    [`(if ,t ,conseq ,alt)
     (evaluate-if t conseq alt r s k)]
    [`(begin . ,e)
     (evaluate-begin e r s k)]
    [`(set! ,var ,val)
     (evaluate-set! var val r s k)]
    [`(lambda ,vars . ,body)
     (evaluate-lambda vars body r s k)]
    [`(,a . ,d)
     (evaluate-application a d r s k)]))

(define (evaluate-if ec et ef r s k)
  (evaluate ec r s
    (lambda (v ss) ;; every object is coded by a function!
      (evaluate ((v 'boolify) et ef) r ss k))))  

(define (evaluate-begin e* r s k)  ;; e* has at least length of 1
  (match e*
    [`(,a . (,d))
     (evaluate a r s (lambda (void ss)
                       (evaluate-begin `(,d) r ss k)))]
    [else (evaluate (car e*) r s k)]))

(define (evaluate-variable n r s k)
  (k (s (r n)) s))

(define (evaluate-set! n e r s k)
  (evaluate e r s
    (lambda (v ss)
      (k v (update ss (r n) v))))) ;; set! exp has a value???

(define (evaluate-application e e* r s k)
  (define (evaluate-arguments e* r s k)
    (if (pair? e*)
        (evaluate (car e*) r s
          (lambda (v ss)
            (evaluate-arguments (cdr e*) r ss
              (lambda (v* sss)
                (k (cons v v*) sss)))))
        (k '() s)))
  (evaluate e r s
    (lambda (f ss)
      (evaluate-arguments e* r ss
        (lambda (v* sss)
          (if (eq? (f 'type) 'function)
              ((f 'behavior) v* sss k)
              (error "Not a function" (car v*))))))))

(define (evaluate-lambda n* e* r s k)
  (allocate 1 s
            (lambda (a* ss)
              (k (create-function
                  (car a*)
                  (lambda (v* s k)
                    (if (= (length n*) (length v*)) ;; only support fixed arity
                        (allocate (length n*) s
                                  (lambda (a* ss)
                                    (evaluate-begin e*
                                      (update* r n* a*)
                                      (update* ss a* v*)
                                      k)))
                        (error "Incorrect arity" (length n*)))))
                 ss))))
#;
(define (evaluate-ftn-lambda n* e* r s k) ;; both way works, but this way doesn't support recursion
  (allocate (+ 1 (length n*)) s
            (lambda (a* ss)
              (k (create-function
                  (car a*)
                  (lambda (v* s k)
                    (if (= (length n*) (length v*))
                        (evaluate-begin e*
                          (update* r n* (cdr a*))
                          (update* s (cdr a*) v*))
                        (error "Incorrect arity" (length n*)))))
                 ss))))
(define (evaluate-quote c r s k)
  (transcode c s k))

(define the-empty-list
  (lambda (msg)
    (case msg
      [(type) 'null]
      [(boolify) (lambda (x y) x)])))

(define (create-boolean value)
  (let ([combinator (if value (lambda (x y) x) (lambda (x y) y))])
    (lambda (msg)
      (case msg
        [(type) 'boolean]
        [(boolify) combinator]))))

(define (create-symbol v)
  (lambda (msg)
    (case msg
      [(type) 'symbol]
      [(name) v]
      [(boolify) (lambda (x y) x)])))
(define (create-number v)
  (lambda (msg)
    (case msg
      [(type) 'number]
      [(value) v]
      [(boolify) (lambda (x y) x)])))
(define (create-string v)
  (lambda (msg)
    (case msg
      [(type) 'string]
      [(value) v]
      [(boolify) (lambda (x y) x)])))
(define (create-function tag behavior)
  (lambda (msg)
    (case msg
      [(type) 'function]
      [(boolify) (lambda (x y) x)]
      [(tag) tag]
      [(behavior) behavior])))
(define (allocate-list v* s q)
  (define (consify v* q)
    (if (pair? v*)
        (consify (cdr v*) (lambda (v ss)
                            (allocate-pair (car v*) v ss q)))
        (q the-empty-list s)))
  (consify v* q))
(define (allocate-pair a d s q)
  (allocate 2 s
            (lambda (a* ss)
              (q (create-pair (car a*) (cadr a*))
                 (update (update ss (car a*) a) (cadr a*) d)))))
(define (create-pair a d)
  (lambda (msg)
    (case msg
      [(type) 'pair]
      [(boolify) (lambda (x y) x)]
      [(set-car) (lambda (s v) (update s a v))]
      [(set-cdr) (lambda (s v) (update s d v))]
      [(car) a]
      [(cdr) d])))

;;-----------------------------------------------------------------
;;                       Initial Environment
;;--------------------------------------------------------------------
(define s.global s.init)
(define r.global r.init)
(define-syntax definitial
  (syntax-rules ()
    [(_ name value)
     (allocate 1 s.global
               (lambda (a* ss)
                 (set! r.global (update r.global 'name (car a*)))
                 (set! s.global (update ss (car a*) value))))]))
(define-syntax defprimitive
  (syntax-rules ()
    [(_ name value arity)
     (definitial name
       (allocate 1 s.global
                 (lambda (a* ss)
                   (set! s.global (expand-store (car a*) ss))
                   (create-function
                    (car a*)
                    (lambda (v* s k)
                      (if (= arity (length v*))
                          (value v* s k)
                          (error "Incorrect arity" 'name)))))))]))
(definitial t (create-boolean #t))
(definitial f (create-boolean #f))
(definitial nil the-empty-list)
(defprimitive <= 
  (lambda (v* s k)
    (if (and (eq? ((car v*) 'type) 'number)
             (eq? ((cadr v*) 'type) 'number))
        (k (create-boolean (<= ((car v*) 'value)
                               ((cadr v*) 'value)))
           s)
        (void)))
  2)
(defprimitive *
  (lambda (v* s k)
    (if (and (eq? ((car v*) 'type) 'number)
             (eq? ((cadr v*) 'type) 'number))
        (k (create-number (* ((car v*) 'value)
                              ((cadr v*) 'value)))
           s)
        (void)))
  2)
(defprimitive =
  (lambda (v* s k)
    (if (and (eq? ((car v*) 'type) 'number)
             (eq? ((cadr v*) 'type) 'number))
        (k (create-boolean (= ((car v*) 'value)
                              ((cadr v*) 'value)))
           s)
        (void)))
  2)
(defprimitive -
  (lambda (v* s k)
    (if (and (eq? ((car v*) 'type) 'number)
             (eq? ((cadr v*) 'type) 'number))
        (k (create-number (- ((car v*) 'value)
                              ((cadr v*) 'value)))
           s)
        (void)))
  2)
(defprimitive cons
  (lambda (v* s k)
    (allocate-pair (car v*) (cadr v*) s k))
  2)
(defprimitive car
  (lambda (v* s k)
    (if (eq? ((car v*) 'type) 'pair)
        (k (s ((car v*) 'car)) s)
        (error "Not a pair" (car v*))))
  1)
(defprimitive set-car!
  (lambda (v* s k)
    (if (eq? ((car v*) 'type) 'pair)
        (let ([pair (car v*)])
          (k pair ((pair 'set-car) s (cadr v*)))) ;; why returns pair as the assignment's result??
        (error "Not a pair" (car v*))))
  2)
(defprimitive set-cdr!
  (lambda (v* s k)
    (if (eq? ((car v*) 'type) 'pair)
        (let ([pair (car v*)])
          (k pair ((pair 'set-cdr) s (cadr v*))))
        (error "Not a pair" (car v*))))
  2)
(defprimitive pair?
  (lambda (v* s k)
    (k (create-boolean (eq? ((car v*) 'type) 'pair)) s))
  1)

(defprimitive eqv?
  (lambda (v* s k)
    (k (create-boolean
        (if (eq? ((car v*) 'type) ((cadr v*) 'type))
            (case ((car v*) 'type)
              [(null) #t]
              [(boolean)
               (((car v*) 'boolify)
                (((cadr v*) 'boolify) #t #f)
                (((cadr v*) 'boolify) #t #f))]
              [(symbol)
               (eq? ((car v*) 'name) ((cadr v*) 'name))]
              [(number)
               (= ((car v*) 'value) ((cadr v*) 'value))]
              [(pair)
               (and (= ((car v*) 'car) ((cadr v*) 'car))
                    (= ((car v*) 'cdr) ((cadr v*) 'cdr)))]
              [(function)
               (= ((car v*) 'tag) ((cadr v*) 'tag))]
              [else #f])
            (void)))
       s))
  2)

;;InPUT and OutPUT and Memory
(define (transcode-back v s)
  (case (v 'type)
    [(null) '()]
    [(boolean) ((v 'boolify) #t #f)]
    [(symbol) (v 'name)]
    [(string) (v 'value)]
    [(number) (v 'value)]
    [(pair) (cons (transcode-back (s (v 'car)) s)
                  (transcode-back (s (v 'cdr)) s))]
    [(function) v]
    [else (error "Unknown type" (v 'type))]))
(define (transcode c s q)
  (cond 
    [(null? c) (q the-empty-list s)]
    [(boolean? c) (q (create-boolean c) s)]
    [(symbol? c) (q (create-symbol c) s)]
    [(string? c) (q (create-string c) s)]
    [(number? c) (q (create-number c) s)]
    [(pair? c)
     (transcode (car c)
                s
                (lambda (a ss)
                  (transcode (cdr c)
                             ss
                             (lambda (d sss)
                               (allocate-pair a d sss q)))))]))

;; start the interpreter
(define (chapter4-interpreter)
  (define (toplevel s)
    (evaluate (read)
      r.global
      s
      (lambda (v ss)
        (display (transcode-back v ss))
        (newline)
        (toplevel ss))))
  (toplevel s.global))
#;
(evaluate '(cons 1 2)
      r.global
      s.global
      (lambda (v ss)
        (display (transcode-back v ss))
        (newline)
        ))
;;==> (1 . 2)

#;
(evaluate '(((lambda (f)
                 ((lambda (mk) (mk mk))
                  (lambda (mk)
                    (f (lambda (x) ((mk mk) x))))))
               (lambda (f)
                 (lambda (n)
                   (if (= n 0)
                       1
                       (* n (f (- n 1)))))))
              5)
    r.global
    s.global
    (lambda (v ss)
      (display (transcode-back v ss))
      (newline)))
; ==> 120
#;
(evaluate '((lambda (f) (eqv? f "hello")) (lambda (x) x))
    r.global
    s.global
    (lambda (v ss)
      (display (transcode-back v ss))
      (newline)))
;=>>>#t        !!!!!!!!!!!!!!!!!!!!!!!!!!! ERROR !!!!!!!!!!!!!!!!!!! needed to be fixed