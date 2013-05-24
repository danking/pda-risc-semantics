#lang racket

(require "abstract.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  pda-term-insn
                  pop-assign?
                  stack-ensure?
                  push?))

(provide (all-defined-out))

(define (lift-insn/astate f)
  (compose f pda-term-insn abstract-state-node))

(define push-astate?         (lift-insn/astate push?))
(define pop-astate?          (lift-insn/astate pop-assign?))
(define stack-ensure-astate? (lift-insn/astate stack-ensure?))
