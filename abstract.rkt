#lang racket
(require "abstract-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         (for-syntax racket racket/syntax))

(provide compute-flow-function
         successor-states
         successor-states/new-stack
         init-astate
         abstract-state-in
         abstract-state-re
         abstract-state-st
         abstract-state-tr
         abstract-state:
         astate-lattice)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; AValue Shorthands

(define avalue-meet (lattice-meet avalue-bounded-lattice))
(define avalue-lte? (lattice-lte? avalue-bounded-lattice))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract Semantics of PDA-RISC Programs

;; A GInsn is [U Insn Insn*]

(define (compute-flow-function t)
  (if (pop-assign-term? t)
      (successor-states/new-stack t)
      (successor-states t)))

;; successor-states/new-stack : Term
;;                              ->
;;                              AStack AState
;;                              ->
;;                              [SetOf AState]
;;
(define (successor-states/new-stack pop-term)
  (match-define (assign _ var _) (pda-term-insn pop-term))
  (define succ-terms (in-set (pda-term-succs pop-term)))

  (define (flow new-stack old-state)
    (match-define (abstract-state: in st tr re) old-state)
    (for/set ([succ-term succ-terms])
      (list succ-term
            (make-abstract-state in new-stack tr (env-set re var st)))))

  flow)

;; eval-pure-rhs : AValue RegisterEnv Pure-Rhs -> AValue
;;
(define (eval-pure-rhs tr re rhs)
  (match rhs
    ((state id)
     (value->avalue rhs))
    ((nterm id)
     (value->avalue rhs))
    ((curr-token _) tr)
    ((register _ uid _ _) (env-get re rhs))))


;; successor-states : Term -> AState -> [SetOf [Pair Term AState]]
(define (successor-states term)
  (define succ-terms (pda-term-succs term))
  (define insn (pda-term-insn term))

  (match insn
    [(assign _ var prhs)
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (list succ-term
                (make-abstract-state in st tr
                                     (env-set re
                                              var
                                              (eval-pure-rhs tr re prhs)))))])]
    [(state-case _ var looks cnsqs)
     (define looks+succ-terms
       (for/list ([succ-term succ-terms])
         (list (possible-lookahead looks cnsqs succ-term)
               succ-term)))
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([look+succ-term looks+succ-terms])
          (define lookahead (first look+succ-term))
          (define succ-term (second look+succ-term))
          (list succ-term
                (make-abstract-state in st tr
                                     (env-refine re var lookahead))))])]
    [(sem-act _ name in-vars out-vars action)
     (when (not (= (length out-vars) 1))
       (warn 'sem-act
             "currently, sem-acts with anything but exactly one argument are "
             "not supported; all arguments after the first will be ignored"))
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (list succ-term
                (make-abstract-state in st tr
                                     (env-set re
                                              (first out-vars)
                                              (value->avalue insn)))))])]
    [(go _ go-target args)
     (for ([succ-term succ-terms])
       (unless (join-point? (pda-term-insn succ-term))
         (error 'go
                "this, ~a, go form is succeded by ~a instead of a join-point"
                term succ-term))
       (match-define (join-point _ join-target params) (pda-term-insn succ-term))
       (unless (equal? go-target join-target)
         (error 'go
                (string-append "this, ~a, go form's target label, ~a, doesn't "
                               "match this join-point, ~a, form's label, ~a")
                term go-target succ-term join-target)))
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (match-define (join-point _ _ params) (pda-term-insn succ-term))
          (list succ-term
                (make-abstract-state in st tr
                                     (env-set/list empty-env
                                                   params
                                                   (map (curry eval-pure-rhs
                                                               tr re)
                                                        args)))))])]
    [(token-case _ looks cnsqs)
     ;; Here we update the token register to the predeceessors tr met with the
     ;; lookahead for this consequent, (tr ⊓ look-tr)
     (define looks+succ-terms
       (for/list ([succ-term succ-terms])
         (list (possible-lookahead looks cnsqs succ-term)
               succ-term)))
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([look+succ-term looks+succ-terms])
          (define lookahead (first look+succ-term))
          (define succ-term (second look+succ-term))
          (define new-tr (avalue-meet tr lookahead))
          (list succ-term
                (make-abstract-state in st new-tr re)))])]
    [(push _ prhs)
     ;; Here we overwrite the stack which is above joined with the
     ;; predecessor's stack. We set it to the join of what was previously there
     ;; with the new stack that we learned about from this push.
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (list succ-term
                (make-abstract-state in (eval-pure-rhs tr re prhs) tr re)))])]
    [(drop-token _)
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (list succ-term
                (make-abstract-state unknown-input st tr re)))])]
    [(get-token _)
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (list succ-term
                (make-abstract-state in st avalue-top re)))])]
    [(if-eos _ cnsq altr)
     (define new-ins+succ-terms
       (for/list ([succ-term succ-terms])
         (list succ-term
               (if (eq? succ-term cnsq)
                   empty-input
                   non-empty-input))))
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([new-in+succ-term new-ins+succ-terms])
          (define succ-term (first new-in+succ-term))
          (define new-in (second new-in+succ-term))
          (list succ-term
                (make-abstract-state new-in st tr re)))])]
    [(reject _)
     (unless (set-empty? succ-terms)
       (error 'reject "reject should have no succesors, has ~a" succ-terms))
     (match-lambda
       [(abstract-state: in st tr re) (set)])]
    [_
     (match-lambda
       [(abstract-state: in st tr re)
        (for/set ([succ-term succ-terms])
          (list succ-term (make-abstract-state in st tr re)))])]))

;; possible-lookahead : [U [ListOf State] [ListOf Symbol]]
;;                      [ListOf Term-Seq*]
;;                      GInsn
;;                      ->
;;                      AValue
;;
;; Returns an AValue representing what we can safely assume about the value
;; case'd on to reach the given branch, indicated by i.
;;
;; NB: If we're in the else branch, we know nothing about the value,
;; i.e. avalue-top.
(define (possible-lookahead looks cnsqs i)
  (let ((res (for/first ([l looks]
                         [c cnsqs]
                         #:when (equal? (first c) i))
               (or (and l (value->avalue l)) avalue-top))))
    (unless res
      (error 'possible-lookahead
             "no csnqs match ~v in ~v"
             i
             cnsqs))
    res))

(define-syntax warn
  (syntax-rules ()
    ((_ id strings ... (vars ...))
     (log-info (string-append "[" (symbol->string id) "] "
                              strings ...
                              "\n")
               vars ...))
    ((_ id strings ...)
     (log-info (string-append "[" (symbol->string id) "] "
                              strings ...
                              "\n")))))
