#lang racket

(require "monads.rkt")
(provide (struct-out monadic-configuration)
         init-configuration
         run-config-monad
         run-config-monad*
         ConfigMonad-bind
         ConfigMonad-return
         ConfigMonad-creator
         ConfigMonad-accessor
         ;; monadic actions
         val->bits
         register-count)

;; a [ConfigMonad X] is a [StateMonad Configuration X]
(struct monadic-configuration (val-bit-hash register-count))

;; ConfigMonad-bind :: [ConfigMonad A] -> (A -> [ConfigMonad B]) -> [ConfigMonad B]
(define ((ConfigMonad-bind command) f)
  (match-define (StateMonad proc) command)
  (StateMonad (lambda (config)
                (define-values (a config2) (proc config))
                (match-define (StateMonad proc2) (f a))
                (proc2 config))))

(define-syntax-rule (ConfigMonad-return x)
  (StateMonad (lambda (config) (values x config))))

(define ConfigMonad-creator StateMonad)
(define ConfigMonad-accessor StateMonad-p)

(define init-val-bit-hash (make-hash '((#f . 1))))
;; [ConfigMonad AValue]
(define (val->bits v)
  (ConfigMonad-creator
   (lambda (config)
     (match-define (monadic-configuration bit-hash _) config)

     (let ((maybe-bits (hash-ref bit-hash v #f)))
       (if maybe-bits
           (values maybe-bits config)
           (let* ((new-bits (hash-ref bit-hash #f)))
             (hash-set! bit-hash v new-bits)
             (hash-set! bit-hash #f (arithmetic-shift new-bits 1))
             (values new-bits config)))))))

;; [ConfigMonad Natural]
(define register-count
  (ConfigMonad-creator
   (lambda (config)
     (values (monadic-configuration-register-count config) config))))

;; [ConfigMonad X] -> [Values X Configuration]
(define (run-config-monad c)
  ((ConfigMonad-accessor c) init-configuration))

(define (run-config-monad* config c)
  ((ConfigMonad-accessor c) config))

(define (init-configuration register-count)
  (monadic-configuration init-val-bit-hash register-count))
