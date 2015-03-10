#lang racket
(require "ch3-04-unwind-protect.rkt")

;; EXercise 1
;; what's the value of (call/cc call/cc)
;; first let's assume the continuation of this exp is k
;; because k(cc ψ) == k(ψ k)
;; k0(cc1 cc2) => k0(cc2 k0) => k0(k0 k0) => k0(k0)

;; Exercise1
#;
((call/cc call/cc) (call/cc call/cc))
;; => k0((cc1 cc2) (cc3 cc4))
;; => k0((cc2 k1) (cc3 cc4)) | k1= k0(_ (cc3 cc4))
;; => k0((k1 k1) (cc3 cc4))
;; => k0(k1 (cc4 k2))  | k2 = k0(k1 _)
;; => k0(k1 (k2 k2))   ;; label A
;; => k0(k1 k2)
;; => k0(k2 (cc3 cc4))
;; => k0(k1 (k2 k2))   ;; the same with label A exp
;; then the expression won't halt, it keep expanding.