#lang racket

(require "abstract.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "../cfa2/bp.rkt")
(provide (all-defined-out))

;; a FlowValue is ...
;; a FlowState is a (make-flow-state [U Term Term*] AState FlowValue)
(struct flow-state (node astate flow-value) #:transparent)

(define (initial-flow-state initial-node initial-fv)
  (flow-state initial-node init-astate initial-fv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (flow-state->node f)
  (flow-state-node f))

(define strip-flow-BP-to-node-BP
  (match-lambda ((BP (flow-state node1 _ _)
                     (flow-state node2 _ _))
                 (BP node1 node2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (lift-insn/flow f)
  (compose f pda-term-insn flow-state-node))

(define (maplift-astate*fv/flow astate-f flow-value-f)
  (match-lambda*
    [(list (flow-state i s1 f1))
     (flow-state i (astate-f s1) (flow-value-f f1))]
    [(list (flow-state i s1 f1) (flow-state i s2 f2))
     (flow-state i (astate-f s1 s2) (flow-value-f f1 f2))]))

(define (foldlift-astate*fv/flow astate-f flow-value-f combine)
  (match-lambda*
    [(list (flow-state i s1 f1))
     (combine i (astate-f s1) (flow-value-f f1))]
    [(list (flow-state i s1 f1) (flow-state i s2 f2))
     (combine i (astate-f s1 s2) (flow-value-f f1 f2))]))

