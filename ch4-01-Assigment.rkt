#lang racket

(require mzlib/compat) ;; to use atom? and getprop
(require compatibility/mlist)

(define (min-max tree)
  (define (first-number tree)
    (if (pair? tree)
        (first-number (car tree))
        tree))
  (let* ([min (first-number tree)]
         [max min])
    (define (scan! tree)
      (cond
        [(pair? tree)
         (scan! (car tree))
         (scan! (cdr tree))]
        [else (if (> tree max) 
                  (set! max tree)
                  (if (< tree min)
                      (set! min tree)
                      (void)))]))
    (scan! tree)
    (list min max)))

(define (make-box value)
  (lambda (msg)
    (case msg
      [(get) value]
      [(set!) (lambda (new-value) (set! value new-value))])))
(define (box-ref box)
  (box 'get))
(define (box-set! box new-value)
  ((box 'set!) new-value))
;test
#;
(let ([name (make-box "Nemo")]
      [winner #f]
      [set-winner! #f])
  (set! winner (lambda () (box-ref name)))
  (set! set-winner! (lambda (new-name) (box-set! name new-name)
                      (box-ref name)))
  (set-winner! "Me")
  (winner))
#;
(define car car);; defining a new car variable is permitted?????
                ;; but not modified the pre-existing one.