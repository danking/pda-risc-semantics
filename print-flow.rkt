#lang racket

(require "flow.rkt"
         "abstract.rkt"
         "../cfa2/cfa2.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt")

(provide (all-defined-out))

(define (flow-state->sexp fs)
  (match fs
    [(flow-state node1 (abstract-state: _ _ _ _ _) flow-value)
     (let ((node-sexp (unparse node1)))
       (list (first node-sexp)
             flow-value
             (rest node-sexp)))]))

(define (pda-risc->flow-annotated-sexp pda-risc uid->fv)
  (define (clear-term t)
    (match t
      ((pda-term _ _ _ _ i) i)))
  (define (annotate-insn i)
    (match i
      ((assign fv id val)
       `(:= ,(uid->fv fv) ,id ,val))
      ((push fv val)
       `(push ,(uid->fv fv) ,val))
      ((sem-act fv name params retvars action)
       `(semantic-action ,(uid->fv fv)
                         ,name
                         ,params
                         ,retvars
                         ,action))
      ((drop-token fv)
       `(drop-token ,(uid->fv fv)))
      ((get-token fv)
       `(get-token ,(uid->fv fv)))
      ((stack-ensure fv hdrm)
       `(stack-ensure ,(uid->fv fv) ,hdrm))
      ((join-point fv label args)
       `(join-point ,(uid->fv fv) ,label . ,args))
      ((block fv insns)
       `(block ,(uid->fv fv) . ,insns))))

  (define (annotate-insn* i)
    (match i
      ((label fv ids stack-types token-types param-lists rhses body)
       `(label ,(uid->fv fv)
               ,(unparse-label-clauses ids stack-types token-types param-lists rhses)
               . ,body))
      ((block* fv insns)
       `(block ,(uid->fv fv) . ,insns))
      ((accept fv vars)
       `(accept ,(uid->fv fv) . ,vars))
      ((reject fv)
       `(reject ,(uid->fv fv)))
      ((if-eos fv cnsq altr)
       `(if-eos ,(uid->fv fv) ,cnsq ,altr))
      ((state-case fv var looks cnsqs)
       `(state-case ,(uid->fv fv)
                    ,var
                    . ,(map (lambda (look cnsq)
                              (cons look cnsq))
                            looks
                            cnsqs)))
      ((token-case fv looks cnsqs)
       `(token-case ,(uid->fv fv)
                    . ,(map (lambda (l c)
                              (cons (if l l #f) c))
                            looks
                            cnsqs)))
      ((go fv target args)
       `(go ,(uid->fv fv) ,target . ,args))))

  (let-values
      (((->sexp _0 _1 _2)
        (traverse-pdarisc #:pdarisc (match-lambda ((pdarisc _ seq) seq))
                          #:term clear-term
                          #:term* clear-term
                          #:insn annotate-insn
                          #:insn* annotate-insn*
                          #:rhs unparse-rhs
                          #:syntax syntax-e
                          #:lbl (lambda (l)
                                  `(label-name ,(label-name-uid l)
                                               ,(label-name-lexical-name l)))
                          #:reg (lambda (r)
                                  `(register ,(register-uid r)
                                             ,(register-lexical-name r))))))
    (->sexp pda-risc)))

(define (displayln-flow-state flow-state)
  (displayln (flow-state->sexp flow-state)))
