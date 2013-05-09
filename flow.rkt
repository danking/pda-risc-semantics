#lang racket

(require "abstract.rkt"
         "../cfa2/cfa2.rkt")
(provide (struct-out flow-state)
         strip-flow-BP-to-node-BP)

;; a FlowValue is ...
;; a FlowState is a (make-flow-state AState FlowValue)
(struct flow-state (astate flow) #:transparent)

(define strip-flow-BP-to-node-BP
  (match-lambda ((BP (flow-state (abstract-state node1 _ _ _ _ _) _)
                     (flow-state (abstract-state node2 _ _ _ _ _) _))
                 (BP node1 node2))))
