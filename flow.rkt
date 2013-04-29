#lang racket

(require "abstract.rkt"
         "../cfa2/cfa2.rkt")
(provide (struct-out flow-state)
         fstate-bp-set->term-bp-set)

;; a FlowValue is ...
;; a FlowState is a (make-flow-state AState FlowValue)
(struct flow-state (astate flow) #:transparent)

(define (fstate-bp-set->term-bp-set bpset)
  (for/set ((bp bpset))
    (match-define (BP (flow-state (abstract-state node1 _ _ _ _ _) _)
                      (flow-state (abstract-state node2 _ _ _ _ _) _))
                  bp)
    (BP node1 node2)))
