#lang racket

(require "monads.rkt"
         (for-syntax syntax/parse))
(provide (contract-out
          [struct monadic-configuration
            ((val-bit-hash (hash/c any/c natural-number/c))
             (register-count natural-number/c)
             (environment (list/c any/c natural-number/c)))])
         ConfigMonad-bind
         ConfigMonad-return
         ConfigMonad-creator
         ConfigMonad-accessor)

;; a [ConfigMonad X] is a [StateMonad Configuration X]

;; a Configuration is a (monadic-configuration [Hash Value Natural]
;;                                             Natural
;;                                             [Pair AEnv TimeStamp])
(struct monadic-configuration (val-bit-hash register-count environment)
        #:transparent)

;; ConfigMonad-bind :: [ConfigMonad A] -> (A -> [ConfigMonad B]) -> [ConfigMonad B]
(define ((ConfigMonad-bind command) f)
  (match-define (StateMonad proc) command)
  (StateMonad (lambda (config)
                (define-values (a config2) (proc config))
                (match-define (StateMonad proc2) (f a))
                (proc2 config))))

(define-syntax (ConfigMonad-return stx)
  (syntax-parse stx
    [(_ body:expr)
     #`(StateMonad (lambda (config)
                     #,(syntax/loc stx (values body config))))]))
(define ConfigMonad-creator StateMonad)
(define ConfigMonad-accessor StateMonad-p)

