#lang racket

(require "monads.rkt"
         "monadic-configuration-data.rkt"
         "monadic-configuration-val-bits.rkt"
         "abstract-register-environment.rkt"
         "time-stamp.rkt")
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
  (monadic-configuration init-val-bit-hash
                         register-count
                         (list (empty-env register-count)
                               initial-time-stamp)))
