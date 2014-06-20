#lang racket
(require "abstract-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "monadic-configuration.rkt"
         (prefix-in monad: "monads.rkt")
         (for-syntax racket
                     racket/syntax
                     syntax/parse))

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

(monad:instantiate-monad-ops
 ConfigMonad-bind ConfigMonad-return ConfigMonad-creator ConfigMonad-accessor
 (~>~ monad:~>~)
 (~> monad:~>)
 (for/set~>~ monad:for/set~>~)
 (for/list~>~ monad:for/list~>~)
 (mapM monad:mapM))

(define-syntax-rule (return x ...) (ConfigMonad-return x ...))
(define-syntax-rule (bind x ...) (ConfigMonad-bind x ...))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; AValue Shorthands

(define avalue-meet (lattice-meet avalue-bounded-lattice))
(define avalue-lte? (lattice-lte? avalue-bounded-lattice))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract Semantics of PDA-RISC Programs

;; A GInsn is [U Insn Insn*]

;; A [FlowFunction T Stack State] is either
;;  - a (Stack State -> [ConfigMonad [SetOf [Pair T State]]]), or
;;  - a (State -> [ConfigMonad [SetOf [Pair T State]]])

;; compute-flow-function : Term -> [ConfigMonad [FlowFunction Term AStack AState]])
(define (compute-flow-function t)
  (if (pop-assign-term? t)
      (successor-states/new-stack t)
      (successor-states t)))

;; successor-states/new-stack : Term
;;                              ->
;;                              [ConfigMonad [FlowFunction Term AStack AState]])
;;
(define (successor-states/new-stack pop-term)
  (match-define (assign _ var _) (pda-term-insn pop-term))
  (define succ-terms (in-set (pda-term-succs pop-term)))

  (define (flow new-stack old-state)
    (match-define (abstract-state: in st tr re) old-state)
    (~> ((new-re (return (env-set re var st))))
      (for/set ([succ-term succ-terms])
        (list succ-term
              (make-abstract-state in new-stack tr new-re)))))

  (return flow))

;; eval-pure-rhs : AValue RegisterEnv Pure-Rhs -> [ConfigMonad AValue]
;;
(define (eval-pure-rhs tr re rhs)
  (match rhs
    ((state id)
     (value->avalue rhs))
    ((nterm id)
     (value->avalue rhs))
    ((curr-token _) (return tr))
    ((register _ uid _ _) (return (env-get re rhs)))))

;; successor-states : Term
;;                    ->
;;                    [ConfigMonad [FlowFunction Term AStack AState]])
;;
(define (successor-states term)
  (define succ-terms (pda-term-succs term))
  (define insn (pda-term-insn term))

  (match insn
    [(assign _ var prhs)
     (return
      (flow-function
       (~> ((value (eval-pure-rhs tr re prhs))
            (new-re (return (env-set re var value))))
         (for/set ([succ-term succ-terms])
           (list succ-term (make-abstract-state in st tr new-re))))))]
    [(state-case _ var looks cnsqs)
     (~> ((succ-terms+looks (for/list~>~ ([succ-term succ-terms])
                              (~> ((lookahead (possible-lookahead looks cnsqs succ-term)))
                                (list succ-term lookahead)))))
       (flow-function
        (for/set~>~ ([s+l succ-terms+looks])
          (~> ((new-re (return (env-refine re var (second s+l)))))
            (list (first s+l) (make-abstract-state in st tr new-re))))))]
    [(sem-act _ name in-vars out-vars action)
     (when (not (= (length out-vars) 1))
       (warn 'sem-act
             "currently, sem-acts with anything but exactly one argument are "
             "not supported; all arguments after the first will be ignored"))
     (return
      (flow-function
       (~> ((aval (value->avalue insn))
            (new-re (return (env-set re (first out-vars) aval))))
         (for/set ([succ-term succ-terms])
           (list succ-term (make-abstract-state in st tr new-re))))))]
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
     (return
      (flow-function
       (~>~ ((values (mapM (curry eval-pure-rhs tr re) args))
             (N register-count))
         (for/set~>~ ([succ-term succ-terms])
           (~> ((new-re (return (env-set/list (empty-env N)
                                              (join-point-params
                                               (pda-term-insn succ-term))
                                              values))))
             (list succ-term (make-abstract-state in st tr new-re)))))))]
    [(token-case _ looks cnsqs)
     ;; Here we update the token register to the predeceessors tr met with the
     ;; lookahead for this consequent, (tr ⊓ look-tr)
     (~> ((succ-terms+looks (for/list~>~ ([succ-term succ-terms])
                              (~> ((lookahead (possible-lookahead looks cnsqs succ-term)))
                                (list succ-term lookahead)))))
       (flow-function
        (return
         (for/set ([s+l succ-terms+looks])
           (list (first s+l)
                 (make-abstract-state in st (avalue-meet tr (second s+l)) re))))))]
    [(push _ prhs)
     ;; Here we overwrite the stack which is above joined with the
     ;; predecessor's stack. We set it to the join of what was previously there
     ;; with the new stack that we learned about from this push.
     (return
      (flow-function
       (~> ((new-st (eval-pure-rhs tr re prhs)))
         (for/set ([succ-term succ-terms])
           (list succ-term (make-abstract-state in new-st tr re))))))]
    [(drop-token _)
     (return
      (flow-function
       (return
        (for/set ([succ-term succ-terms])
          (list succ-term (make-abstract-state unknown-input st tr re))))))]
    [(get-token _)
     (return
      (flow-function
       (return
        (for/set ([succ-term succ-terms])
          (list succ-term (make-abstract-state in st avalue-top re))))))]
    [(if-eos _ cnsq altr)
     (define succ-terms+new-ins
       (for/list ([succ-term succ-terms])
         (list succ-term
               (if (eq? succ-term cnsq)
                   empty-input
                   non-empty-input))))
     (return
      (flow-function
       (return
        (for/set ([s+i succ-terms+new-ins])
          (list (first s+i) (make-abstract-state (second s+i) st tr re))))))]
    [(reject _)
     (unless (set-empty? succ-terms)
       (error 'reject "reject should have no succesors, has ~a" succ-terms))
     (return
      (flow-function
       (return (set))))]
    [_
     (return
      (flow-function
       (return
        (for/set ([succ-term succ-terms])
          (list succ-term (make-abstract-state in st tr re))))))]))

;; possible-lookahead : [U [ListOf State] [ListOf Symbol]]
;;                      [ListOf Term-Seq*]
;;                      GInsn
;;                      ->
;;                      [ConfigMonad AValue]
;;
;; Returns an AValue representing what we can safely assume about the value
;; case'd on to reach the given branch, indicated by i.
;;
;; NB: If we're in the else branch, we know nothing about the value,
;; i.e. avalue-top.
(define (possible-lookahead looks cnsqs i)
  (define lookahead
    (for/first ([l looks]
                [c cnsqs]
                #:when (equal? (first c) i))
      (if l (value->avalue l) (return avalue-top))))
  (unless lookahead
    (error 'possible-lookahead
           "no csnqs match ~v in ~v (~a)"
           i
           cnsqs
           lookahead))
  lookahead)

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

(define-syntax (flow-function stx)
  (syntax-parse stx
    [(_ body:expr)
     (let ((variable-bindings (map (curry datum->syntax #'body) '(in st tr re))))
       #`(match-lambda
           [(abstract-state: #,@variable-bindings) body]))]))
