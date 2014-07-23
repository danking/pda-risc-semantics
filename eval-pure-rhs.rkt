#lang racket

(require "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "abstract-data.rkt"
         "monadic-configuration.rkt"
         )
(provide eval-pure-rhs
         eval-pure-rhs/no-monad
         )


(define-syntax-rule (return x ...) (ConfigMonad-return x ...))


;; eval-pure-rhs : AValue Pure-Rhs -> [ConfigMonad AValue]
;;
(define (eval-pure-rhs tr rhs)
  (match rhs
    ((state id)
     (value->avalue rhs))
    ((nterm id)
     (value->avalue rhs))
    ((curr-token _) (return tr))
    ((register _ uid _ _) (env-get rhs))))

;; eval-pure-rhs/no-monad : State Pure-Rhs Configuration -> AValue
;;
(define (eval-pure-rhs/no-monad sigma rhs config)
  (run-config-monad* config (eval-pure-rhs (abstract-state-tr sigma) rhs)))
