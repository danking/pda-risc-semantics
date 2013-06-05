#lang racket
(require "abstract.rkt"
         "abstract-data.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         (for-syntax racket racket/syntax))

(provide abstract-backstep)

;; abstract-step : AState -> [SetOf AState]
;; Simply walks the predecessors, ignoring the other components of the abstract
;; state. If/when an analysis can be informed by more information, this should
;; be developed further.
(define abstract-backstep
  (match-lambda
    ((abstract-state (pda-term preds _ _ _ insn) in st tr re le)
     (for/seteq ([pred preds]) (abstract-state pred in st tr re le)))))
