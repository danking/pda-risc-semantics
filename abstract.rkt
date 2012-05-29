#lang racket
(require "../cfa2/cfa2.rkt"
         "../racket-utils/singleton-struct.rkt"
         (only-in "../cfa2/utilities.rkt" bpset->fv-hash)
         (only-in "../racket-utils/similar-sets.rkt" get-basic-set)
         (rename-in "../pda-to-pda-risc/risc-enhanced/data.rkt")
         (for-syntax racket racket/syntax))

(provide abstract-step
         abstract-step/new-stack
         init-astate
         abstract-state
         abstract-state?
         abstract-state-node
         abstract-state-in
         abstract-state-st
         abstract-state-tr
         abstract-state-re
         abstract-state-le)

;; An AState is a
;;  (abstract-state [U Term Term*]
;;                  AInStream
;;                  AValue
;;                  AValue
;;                  ARegisterEnv
;;                  LblClosureEnv)
(struct abstract-state (node in st tr re le) #:transparent)
;; where,
;;   - node is the pda-term
;;   - in is the input straem
;;   - st is the stack
;;   - tr is the token register
;;   - re is the register environment (besides the token register)
;;   - le is the label closure environment (all the values in scope when
;;     the labeled codepoint was created)
(define (init-astate node)
  (abstract-state node
                  unknown-input
                  (set)
                  (set)
                  empty-env
                  empty-env))


;; an ARegisterEnv is a [Hash UID AValue]
(define empty-env (hash))
(define env-get hash-ref)
(define env-set hash-set)
(define (env-set/list env vars vals)
  (for/fold ([env env])
            ([var vars]
             [val vals])
    (env-set env var val)))
(define (env-set/all-to env vars val)
  (for/fold ([env env])
            ([var vars])
    (env-set env var val)))
;; a UID is a number from the register data structure
;;
;; a LblClosureEnv is a [Hash LabelName ARegisterEnv]

;; an AValue is a [SetOf Value]
;;
;; a Value is either:
;;   - StateVal
;;   - NTerm
;;   - SemActVal
;;   - Token
;;   - UnknownInput
;;   - Bottom
(singleton-struct bottom)
(define avalue-⊑ subset?)

;; an AInStream is [U UnknownInput NonEmptyInput EmptyInput]
;;
(singleton-struct unknown-input)
(singleton-struct non-empty-input)
(singleton-struct empty-input)

;; a SemActVal is how we represent the result of a sem-act:
;;   (sem-act-val [Syntax Id] [ListOf Value])
(struct sem-act-val (name args) #:transparent)

;; A GInsn is [U Insn Insn*]

;; eval-pure-rhs : AValue RegisterEnv Pure-Rhs -> AValue
(define (eval-pure-rhs tr re rhs)
  (match rhs
    ((state id) (set rhs))
    ((nterm id) (set rhs))
    ((curr-token _) tr)
    ((register _ uid _ _) (env-get re rhs))))

;; abstract-step : AState -> [SetOf AState]
(define abstract-step
  (match-lambda
    ((and as (abstract-state (pda-term _ _ _ _ i) in st tr re le))
     (unless tr
       (warn 'abstract-step
             "I don't expect tr to ever be false in: ~v"
             (as)))
     (abstract-step/new-stack as (step-stack st i (curry eval-pure-rhs tr re))))))

;; abstract-step : AState AStack -> [SetOf Astate]
(define abstract-step/new-stack
  (match-lambda**
    (((abstract-state (pda-term _ succs _ _ i) in st tr re le) next-stack)
     (for/seteq ([t^ succs]
                 #:when (valid-succ-state? t^ i in st tr re le))
       (match-let (((pda-term _ _ _ _ i^) t^))
         (abstract-state t^
                         (step-input in i i^)
                         next-stack
                         (step-token-reg tr i i^ in)
                         (step-reg-env re i i^
                                       st (curry eval-pure-rhs tr re) le)
                         (step-lbl-env le i i^ re)))))))

;; valid-succ-state? : AState
;;                     GInsn
;;                     AInStrem
;;                     AStack
;;                     AValue
;;                     ARegisterEnv
;;                     LblClosureEnv
;;                     ->
;;                     Boolean
(define (valid-succ-state? t^ i in st tr re le)
  (match-define (pda-term _ _ _ _ i^) t^)
  (match* (i tr in re)
    (((token-case _ looks cnsqs) tr _ _)
     (for/or ((tr tr)) (unknown-input? tr)))
    (((get-token _) _ in _)
     (non-empty-input? in))
    (((state-case _ var looks cnsqs) _ _ re)
     (let ((l (matching-lookahead looks cnsqs i^))
           (aval (env-get re var)))
       (avalue-⊑ l aval)))
    ((_ _ _ _) #t)))

;; step-input : AInStream GInsn GInsn -> AInStream
(define step-input
  (match-lambda**
    ((_ (drop-token _) _)
     unknown-input)
    ((_ (if-eos _ cnsq altr) t^)
     (if (eq? t^ cnsq)
         empty-input
         non-empty-input))
    ((in _ _) in)))

;; step-stack : AStack GInsn (Pure-Rhs -> AValue) -> AStack
(define step-stack
  (match-lambda**
    ((_ (push _ prhs) eval-prhs) (eval-prhs prhs))
    ((_ (assign _ var (pop)) _)
     (error 'step-stack
            "found a pop node, this should have been caught earlier"))
    ((st _ _) st)))

;; step-token-reg : AValue GInsn GInsn AInStream -> AValue
(define step-token-reg
  (match-lambda**
   ((tr (get-token _) _ in)
    (when (not (non-empty-input? in))
      (warn 'step-token-reg
            "tried to get-token when the input stream was not in the "
            "non-empty-input state, was: ~a ; this is prevented by using the "
            "`if-eos' form prior to a use of `(get-token)'"
            (in)))
    (if (non-empty-input? in)
        (set unknown-input)
        (set bottom)))
   ((tr (drop-token _) _ _) (set bottom))
   ((tr (token-case _ looks cnsqs) i^ _)
    (when (not (for/or ((t tr)) (unknown-input? t)))
      (warn 'step-token-reg
            "tried to token-case when tr wasn't unknown-input, was: ~a; all "
            "uses of the token register should be preceeded by a `(get-token)'"
            (tr)))
    (matching-lookahead looks cnsqs i^))
   ((tr _ _ _) tr)))

;; step-reg-env : ARegisterEnv
;;                GInsn
;;                GInsn
;;                AStack
;;                (Pure-Rhs -> AValue)
;;                LblClosureEnv
;;                ->
;;                ARegisterEnv
(define step-reg-env
  (match-lambda**
    ((re (sem-act _ name in-vars out-vars action) _ _ _ _)
     (when (not (= (length out-vars) 1))
       (warn 'step-reg-env
             "currently, sem-acts with anything but exactly one argument are "
             "not supported; all arguments after the first will be ignored"))
     (if (or (empty? out-vars) (false? (first out-vars)))
         re
         (env-set re (first out-vars) (set (sem-act-val name in-vars)))))
    ((re (assign _ var (pop)) _ st _ _)
     (env-set re var st))
    ((re (assign _ var prhs) _ _ eval-prhs _)
     (env-set re var (eval-prhs prhs)))
    ((re (and i (state-case _ var looks cnsqs)) i^ _ _ _)
     (let ((l (matching-lookahead looks cnsqs i^))
           (aval (env-get re var)))
       (when (not (avalue-⊑ l aval))
         (warn 'step-reg-env
               "in the form: ~a, the var, ~a, has abstract value: ~a, which "
               "implies that the branch, ~a, gaurded by ~a is unreachable; "
               "you should investigate why that branch seems unreachable to "
               "the abstract evaluation"
               (i var aval i^ l)))
       (env-set re var (matching-lookahead looks cnsqs i^))))
    ((re (go _ target args) (join-point _ target params) _ _ le)
     (env-set/list (env-get le target) args params))
    ((re (and g (go _ target _))
         (and j (join-point _ lbl _))
         _ _ _)
     (error 'step-reg-env
            (string-append "this, ~a, go form's target label, ~a, doesn't match this "
                           "join-point, ~a, form's label, ~a")
            g target j lbl))
    ((re (and g (go _ _ _)) i^ _ _ _)
     (error 'step-reg-env
            "this, ~a, go form is succeded by ~a instead of a join-point"
            (g i^)))
    ((re _ _ _ _ _) re)))

;; step-lbl-env : LblClosureEnv GInsn GInsn ARegisterEnv -> LblClosureEnv
(define step-lbl-env
  (match-lambda**
    ((le (label _ ids _ _ _ _ _) _ re)
     (env-set/all-to le ids re))
    ((le _ _ _) le)))

;; matching-lookahead : [ListOf State] [ListOf Term-Seq*] -> AValue
(define (matching-lookahead looks cnsqs i)
  (let ((res
         (for/first ([l looks]
                     [c cnsqs]
                     #:when (eq? (pda-term-insn (first c)) i))
           (if l (set l) (set unknown-input)))))
    (unless res
      (error 'matching-lookahead
             "no csnqs match ~v in ~v"
             i
             cnsqs))
    res))
;; TODO: this should actually represent some TOP value, for "it could be anything"

(define-syntax warn
  (syntax-rules ()
    ((_ id strings ... (vars ...))
     (printf (string-append "[" (symbol->string id) "] "
                            strings ...
                            "\n")
             vars ...))
    ((_ id strings ...)
     (printf (string-append "[" (symbol->string id) "] "
                            strings ...
                            "\n")))))
