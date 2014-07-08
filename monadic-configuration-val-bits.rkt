#lang racket

(provide init-val-bit-hash
         val->bits)

(require "monadic-configuration-data.rkt")

(define init-val-bit-hash (make-hash '((#f . 1))))
;; [ConfigMonad AValue]
(define (val->bits v)
  (ConfigMonad-creator
   (lambda (config)
     (match-define (monadic-configuration bit-hash _ _) config)

     (let ((maybe-bits (hash-ref bit-hash v #f)))
       (if maybe-bits
           (values maybe-bits config)
           (let* ((new-bits (hash-ref bit-hash #f)))
             (hash-set! bit-hash v new-bits)
             (hash-set! bit-hash #f (arithmetic-shift new-bits 1))
             (values new-bits config)))))))

