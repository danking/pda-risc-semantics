#lang racket
(require "abstract-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         (for-syntax racket racket/syntax))

(provide abstract-step
         abstract-step/new-stack
         init-astate
         (struct-out abstract-state)
         abstract-state:
         astate-bounded-lattice
         astate-same-sub-lattice?
         astate-sub-lattice-hash-code)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sub-Lattices in the Abstract State Lattice

(define (astate-same-sub-lattice? as1 as2 [recur equal?])
  (= (pda-term->uid (abstract-state-node as1))
     (pda-term->uid (abstract-state-node as2))))

(define (astate-sub-lattice-hash-code as [recur equal-hash-code])
  (recur (pda-term->uid (abstract-state-node as))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract Semantics of PDA-RISC Programs

;; A GInsn is [U Insn Insn*]

;; eval-pure-rhs : AValue RegisterEnv [MutableHash Value Natural] Pure-Rhs -> AValue
(define (eval-pure-rhs tr re val->bits rhs)
  (match rhs
    ((state id)
     (value->avalue rhs val->bits))
    ((nterm id)
     (value->avalue rhs val->bits))
    ((curr-token _) tr)
    ((register _ uid _ _) (env-get re rhs))))

;; abstract-step : AState -> [SetOf AState]
(define/match (abstract-step as)
  [((abstract-state: (pda-term _ _ _ _ i) in st tr re le val->bits))
   (unless tr
     (warn 'abstract-step
           "I don't expect tr to ever be false in: ~v"
           (as)))
   (abstract-step/new-stack as (step-stack st i (curry eval-pure-rhs
                                                       tr
                                                       re
                                                       val->bits)))])

;; abstract-step : AState AStack -> [SetOf Astate]
(define/match (abstract-step/new-stack astate astack)
  [((abstract-state: (pda-term _ succs _ _ i) in st tr re le val->bits) next-stack)
   (for/seteq ([t^ succs]
               #:when (valid-succ-state? t^ i in st tr re le val->bits))
     (match-let (((pda-term _ _ _ _ i^) t^))
       ;; mutate the register environment for the entire program
       (step-reg-env! re i i^ st (curry eval-pure-rhs tr re) le val->bits)
       ;; mutate the label environment for the entire program
       ;; TODO, this is a total hack, the label environment should not use the
       ;; same semantics as the register environemnt, there's no joining.
       (step-lbl-env! le i i^ re val->bits)
       (make-abstract-state t^
                            (step-input in i i^)
                            next-stack
                            (step-token-reg tr i i^ in val->bits)
                            re
                            le
                            val->bits)))])

;; valid-succ-state? : [U Term Term*]
;;                     GInsn
;;                     AInStrem
;;                     AStack
;;                     AValue
;;                     ARegisterEnv
;;                     LblClosureEnv
;;                     [MutableHash Value Natural]
;;                     ->
;;                     Boolean
(define (valid-succ-state? t^ i in st tr re le val->bits)
  (match-define (pda-term _ _ _ _ i^) t^)
  (match* (i tr in re)
    (((token-case _ looks cnsqs) tr _ _)
     (let ((l (required-lookahead looks cnsqs i^ val->bits)))
       (log-if-false ((lattice-lte? avalue-bounded-lattice) l tr)
                     "in token-case ~a\n the look is ~a, tr is ~a"
                     i
                     (avalue->value-set l val->bits)
                     (avalue->value-set tr val->bits))))
    (((get-token _) _ in _)
     (non-empty-input? in))
    (((state-case _ var looks cnsqs) _ _ re)
     (let ((l (required-lookahead looks cnsqs i^ val->bits))
           (aval (env-get re var)))
       ((lattice-lte? avalue-bounded-lattice) l aval)))
    ((_ _ _ _) #t)))

;; step-input : AInStream GInsn GInsn -> AInStream
(define/match (step-input ainstream i1 i2)
  [(_ (drop-token _) _)
   unknown-input]
  [(_ (if-eos _ cnsq altr) _)
   (if (eq? i2 cnsq) empty-input non-empty-input)]
  [(in _ _) in])

;; step-stack : AStack GInsn (Pure-Rhs -> AValue) -> AStack
(define (step-stack st i eval-prhs)
  (match i
    [(push _ prhs)
     (eval-prhs prhs)]
    [(assign _ var (pop))
     (error 'step-stack
          "found a pop node, this should have been caught earlier")]
    [_ st]))

;; step-token-reg : AValue GInsn GInsn AInStream [MutableHash Value Natural] -> AValue
(define (step-token-reg tr i1 i2 in val->bits)
  (match i1
    [(get-token _)
     (when (not (non-empty-input? in))
       (warn 'step-token-reg
             "tried to get-token when the input stream was not in the "
             "non-empty-input state, was: ~a ; this is prevented by using the "
             "`if-eos' form prior to a use of `(get-token)'"
             (in)))
     (if (non-empty-input? in)
         avalue-top
         avalue-bottom)]
    [(drop-token _) avalue-bottom]
    [(token-case _ looks cnsqs)
     (when (not (avalue-top? tr))
       (warn 'step-token-reg
             "tried to token-case when tr wasn't top, was: ~a; all "
             "uses of the token register should be preceeded by a `(get-token)'"
             (tr)))
     ((lattice-meet avalue-bounded-lattice) (possible-lookahead looks
                                                                cnsqs
                                                                i2
                                                                val->bits)
                                            tr)]
    [_ tr]))

;; step-reg-env! : ARegisterEnv
;;                 GInsn
;;                 GInsn
;;                 AStack
;;                 (Pure-Rhs -> AValue)
;;                 LblClosureEnv
;;                 [MutableHash Value Natural]
;;                 ->
;;                 Void
(define (step-reg-env! re i1 i2 st eval-prhs le val->bits)
  (match* (i1 i2)
    [((sem-act _ name in-vars out-vars action) i2)
     (when (not (= (length out-vars) 1))
       (warn 'step-reg-env
             "currently, sem-acts with anything but exactly one argument are "
             "not supported; all arguments after the first will be ignored"))
     (unless (or (empty? out-vars) (false? (first out-vars)))
       (env-set! re (first out-vars)
                 (value->avalue i1 val->bits)))]
    [((assign _ var (pop)) i2)
     (env-set! re var st)]
    [((assign _ var prhs) i2)
     (env-set! re var (eval-prhs prhs))]
    [((state-case _ var looks cnsqs) i2)
     (let ((l (possible-lookahead looks cnsqs i2 val->bits))
           (aval (env-get re var)))
       (env-set! re var ((lattice-meet avalue-bounded-lattice) l aval)))]
    [((go _ target args) (join-point _ target params))
     (env-set/list! re args params)]
    [((go _ target _) (join-point _ lbl _))
     (error 'step-reg-env
            (string-append "this, ~a, go form's target label, ~a, doesn't match this "
                           "join-point, ~a, form's label, ~a")
            i1 target i2 lbl)]
    [((go _ _ _) _)
     (error 'step-reg-env
            "this, ~a, go form is succeded by ~a instead of a join-point"
            i1 i2)]
    [(_ _)
     (void)]))

;; step-lbl-env! : LblClosureEnv GInsn GInsn ARegisterEnv -> Void
(define step-lbl-env!
  (match-lambda**
    ;; ((le (label _ ids _ _ _ _ _) _ re)
    ;;  (for ([id ids])
    ;;    (hash-set! le id re)))
    ((le _ _ _ _) le)))

;; matching-lookahead : [U [ListOf State] [ListOf Symbol]]
;;                      [ListOf Term-Seq*]
;;                      GInsn
;;                      AValue
;;                      [MutableHash Value Natural]
;;                      ->
;;                      AValue
;;
;; Returns the lookahead that matches the given branch, indicated by i. If the
;; branch is guarded by the else lookahead, base is used.
(define (matching-lookahead looks cnsqs i base val->bits)
  (let ((res (for/first ([l looks]
                         [c cnsqs]
                         #:when (eq? (pda-term-insn (first c)) i))
               (or (and l (value->avalue l val->bits)) base))))
    (unless res
      (error 'matching-lookahead
             "no csnqs match ~v in ~v"
             i
             cnsqs))
    res))

;; required-lookahead : [U [ListOf State] [ListOf Symbol]]
;;                      [ListOf Term-Seq*]
;;                      GInsn
;;                      [MutableHash Value Natural]
;;                      ->
;;                      AValue
;;
;; Returns an AValue representing the minimum AValue which would permit
;; execution to enter the given branch, indicated by i.
;;
;; NB: If we're in the else branch, nothing is required, i.e. avalue-bottom
(define (required-lookahead looks cnsqs i val->bits)
  (matching-lookahead looks cnsqs i avalue-bottom val->bits))

;; possible-lookahead : [U [ListOf State] [ListOf Symbol]]
;;                      [ListOf Term-Seq*]
;;                      GInsn
;;                      [MutableHash Value Natural]
;;                      ->
;;                      AValue
;;
;; Returns an AValue representing what we can safely assume about the value
;; case'd on to reach the given branch, indicated by i.
;;
;; NB: If we're in the else branch, we know nothing about the value,
;; i.e. avalue-top.
(define (possible-lookahead looks cnsqs i val->bits)
  (matching-lookahead looks cnsqs i avalue-top val->bits))

;; TODO: this should actually represent some TOP value, for "it could be anything"

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

(define-syntax log-if-false
  (syntax-rules ()
    ((_ bool str args ...)
     (begin (unless bool
              (log-info str args ...))
            bool))))
