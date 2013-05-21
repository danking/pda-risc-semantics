#lang racket

(require "abstract.rkt"
         "abstract-register-environment.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-term-insn
                  pop-assign?
                  stack-ensure?
                  push?))

(provide (all-defined-out))

;; astate-similar? : AState AState -> Boolean
(define astate-similar? (match-lambda*
                          [(list (abstract-state term1 in1 st1 tr1 re1 le1)
                                 (abstract-state term2 in2 st2 tr2 re2 le2))
                           (and (equal? term1 term2)
                                (equal? st1 st2))]))
;; astate-hash-code : AState -> Number
(define astate-hash-code (match-lambda
                           [(abstract-state term in st tr re le)
                            (+ (equal-hash-code term)
                               (equal-hash-code st))]))
;; astate-equal? : AState AState -> Boolean
(define astate-equal? (match-lambda*
                        [(list (abstract-state term1 in1 st1 tr1 re1 le1)
                               (abstract-state term2 in2 st2 tr2 re2 le2))
                         (and (equal? term1 term2)
                              (equal? re1 re2)
                              (equal? st1 st2))]))

;; astate-join : AbstractState AbstractState -> AbstractState
(define astate-join
  (match-lambda*
    [(list (abstract-state t in st tr1 re1 le)
           (abstract-state t in st tr2 re2 le))
     (abstract-state t in st
                     (set-union tr1 tr2)
                     (register-env-join re1 re2)
                     le)]
    [(list (and a1 (abstract-state t1 in1 st1 tr1 re1 le1))
           (and a2 (abstract-state t2 in2 st2 tr2 re2 le2)))
     (error 'astate-join
            (string-append "States must have matching nodes, stacks, "
                           "and label environment. Given ~v and ~v.")
            a1 a2)]))

;; astate-gte : AbstractState AbstractState -> Boolean
(define astate-gte
  (match-lambda*
    [(list (abstract-state t in st tr1 re1 le)
           (abstract-state t in st tr2 re2 le))
     (and (equal? re1 (register-env-join re1 re2))
          (equal? tr1 (set-union tr1 tr2)))]
    [(list (abstract-state _ _ _ _ _ _)
           (abstract-state _ _ _ _ _ _))
     #f]))

(define (lift-insn/astate f)
  (compose f pda-term-insn abstract-state-node))

(define push-astate?         (lift-insn/astate push?))
(define pop-astate?          (lift-insn/astate pop-assign?))
(define stack-ensure-astate? (lift-insn/astate stack-ensure?))
