#lang racket

(require "abstract.rkt"
         "abstract-utilities.rkt"
         "../cfa2/bp.rkt")
(provide (all-defined-out))

;; a FlowValue is ...
;; a FlowState is a (make-flow-state AState FlowValue)
(struct flow-state (astate flow-value) #:transparent)

(define (initial-flow-state initial-node initial-fv)
  (flow-state (init-astate initial-node) initial-fv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (flow-state->node f)
  (abstract-state-node (flow-state-astate f)))

(define strip-flow-BP-to-node-BP
  (match-lambda ((BP (flow-state (abstract-state node1 _ _ _ _ _) _)
                     (flow-state (abstract-state node2 _ _ _ _ _) _))
                 (BP node1 node2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Flow State Similarness

;; flow-state-similar? : FlowState FlowState -> Boolean
(define flow-state-similar? (match-lambda*
                              [(list (flow-state s1 _)
                                     (flow-state s2 _))
                               (astate-similar? s1 s2)]))
;; flow-state-hash-code : FlowState -> Number
(define flow-state-hash-code (match-lambda
                               [(flow-state as _) (astate-hash-code as)]))
;; flow-state-equal? : FlowState FlowState -> Boolean
(define flow-state-equal? (match-lambda*
                            [(list (flow-state s1 _)
                                   (flow-state s2 _))
                             (astate-equal? s1 s2)]))

(define (lift-insn/flow f)
  (compose (lift-insn/astate f) flow-state-astate))

(define (maplift-astate*fv/flow astate-f flow-value-f)
  (match-lambda*
    [(list (flow-state s1 f1))
     (flow-state (astate-f s1) (flow-value-f f1))]
    [(list (flow-state s1 f1) (flow-state s2 f2))
     (flow-state (astate-f s1 s2) (flow-value-f f1 f2))]))

(define (foldlift-astate*fv/flow astate-f flow-value-f combine)
  (match-lambda*
    [(list (flow-state s1 f1))
     (combine (astate-f s1) (flow-value-f f1))]
    [(list (flow-state s1 f1) (flow-state s2 f2))
     (combine (astate-f s1 s2) (flow-value-f f1 f2))]))

