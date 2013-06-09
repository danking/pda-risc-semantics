#lang racket
(require "abstract-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         (for-syntax racket racket/syntax))

(provide successor-states
         successor-states/new-stack
         init-astate
         init-configuration
         abstract-state-node
         abstract-state-in
         abstract-state-re
         abstract-state-st
         abstract-state-tr
         abstract-state:
         astate-lattice
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

;; successor-states/new-stack : AState AState AState Configuration
;;                              ->
;;                              [Values [SetOf AState] Configuration]
;;
(define/match (successor-states/new-stack gp push pop config)
  [(_
    (abstract-state: push-term push-in _ _ _)
    (abstract-state: pop-term pop-in _ _ _)
    (configuration: global-re _ stack-map _ tr-map _ val->bits))
   (match-define (assign _ var _) (pda-term-insn pop-term))

   (let* ((new-stack (env-get (configuration-stack-map config) push-term))
          (new-re-config (config/re-set config var new-stack)))
     (for/fold ((succ-states (set))
                (config new-re-config))
         ((succ-term (in-set (pda-term-succs pop-term))))
       (let ((config (config/update-st config succ-term new-stack)))
         (values (set-add succ-states (stamped-state succ-term pop-in config))
                 config))))])

(define/match (successor-states push node config)
  [(_
    (abstract-state: term in _ _ _)
    (configuration: global-re _ stack-map _ tr-map _ val->bits))
   (for/fold ([successor-state-set (set)]
              [config config])
       ([successor-term (in-set (pda-term-succs term))]
        #:when (valid-succ-state? node successor-term config))
     (let-values (((successor-state config)
                   (abstract-step node successor-term config)))
       (values (set-add successor-state-set successor-state) config)))])

(define/match (abstract-step pred succ-term config)
  [((abstract-state: pred-term pred-in _ _ _)
    _
    (configuration: config-re _ stack-map _ tr-map _ val->bits))

   ;; we use the predecessor tr and re because we don't have any recursive
   ;; binding, all free variables refer to bindings from predecssor terms
   (define eval-prhs (curry eval-pure-rhs
                            (env-get (configuration-tr-map config) pred)
                            (configuration-re config)
                            val->bits))

   (define (config-step/stack config)
     (config/update-st config succ-term (env-get stack-map pred-term)))
   (define (config-step/tr config)
     (config/update-tr config succ-term (env-get tr-map pred-term)))
   (define config-step/stack&tr (compose config-step/stack config-step/tr))

   ;; note that we capture the binding of succ-term in in+config
   (define (in+config in config)
     (values (stamped-state succ-term in config) config))

   (match (pda-term-insn pred-term)
     [(assign _ var prhs)
      (in+config pred-in (config/re-set (config-step/stack&tr config)
                                        var
                                        (eval-prhs prhs)))]
     [(state-case _ var looks cnsqs)
      (in+config pred-in
                 (config/re-set (config-step/stack&tr config)
                                var
                                (avalue-meet (possible-lookahead looks
                                                                 cnsqs
                                                                 succ-term
                                                                 val->bits)
                                             (env-get config-re var))))]
     [(sem-act _ name in-vars out-vars action)
      (when (not (= (length out-vars) 1))
        (warn 'sem-act
              "currently, sem-acts with anything but exactly one argument are "
              "not supported; all arguments after the first will be ignored"))
      (in+config pred-in
                 (config/re-set (config-step/stack&tr config)
                                (first out-vars)
                                (value->avalue (pda-term-insn pred-term)
                                               val->bits)))]
     [(go _ go-target args)
      (unless (join-point? (pda-term-insn succ-term))
        (error 'go
               "this, ~a, go form is succeded by ~a instead of a join-point"
               pred-term succ-term))
      (match-define (join-point _ join-target params) (pda-term-insn succ-term))
      (unless (equal? go-target join-target)
        (error 'go
               (string-append "this, ~a, go form's target label, ~a, doesn't "
                              "match this join-point, ~a, form's label, ~a")
               pred-term go-target succ-term join-target))
      (in+config pred-in
                 (config/re-set/list (config-step/stack&tr config)
                                     params
                                     (map eval-prhs args)))]
     [(token-case _ looks cnsqs)
      ;; Here we update the token register to the predeceessors tr met with the
      ;; lookahead for this consequent, (pred-tr ⊓ look-tr)
      (let* ((pred-tr (env-get tr-map pred-term))
             (lookahead (possible-lookahead looks cnsqs succ-term val->bits))
             (new-tr (avalue-meet pred-tr lookahead)))
        (in+config pred-in
                   (config/update-tr (config-step/stack config)
                                     succ-term
                                     new-tr)))]
     [(push _ prhs)
      ;; Here we overwrite the stack which is above joined with the
      ;; predecessor's stack. We set it to the join of what was previously there
      ;; with the new stack that we learned about from this push.
      (in+config pred-in
                 (config/update-st (config-step/stack&tr config)
                                   succ-term
                                   (eval-prhs prhs)))]
     [(drop-token _)
      (in+config unknown-input (config-step/stack&tr config))]
     [(get-token _)
      (in+config pred-in
                 (config/update-tr (config-step/stack&tr config)
                                   succ-term
                                   avalue-top))]
     [(if-eos _ cnsq altr)
      (in+config (if (eq? succ-term cnsq) empty-input non-empty-input)
                 (config-step/stack&tr config))]
     [(reject _)
      (error 'reject "reject should have no succesors, has ~a" succ-term)]
     [_ (in+config pred-in (config-step/stack&tr config))])])

(define avalue-meet (lattice-meet avalue-bounded-lattice))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Some shorthands for configuration stuff
(define (stamped-state term in config)
  (make-abstract-state term in
                       (configuration:stack-time config term)
                       (configuration:tr-time config term)
                       (configuration-re-time config)))
(define (config/re-set c reg val)
  (configuration:update-re c reg val))
(define (config/re-set/list c regs vals)
  (configuration:update-re/list c regs vals))
(define (config/update-tr c succ-term new-tr)
  (configuration:update-tr-map c succ-term new-tr))
(define (config/update-st c succ-term new-st)
  (configuration:update-stack-map c succ-term new-st))

;; eval-pure-rhs : AValue RegisterEnv [MutableHash Value Natural] Pure-Rhs
;;                 ->
;;                 AValue
(define (eval-pure-rhs tr re val->bits rhs)
  (match rhs
    ((state id)
     (value->avalue rhs val->bits))
    ((nterm id)
     (value->avalue rhs val->bits))
    ((curr-token _) tr)
    ((register _ uid _ _) (env-get re rhs))))

;; valid-succ-state? : [U Term Term*]
;;                     GInsn
;;                     Configuration
;;                     ->
;;                     Boolean
(define/match (valid-succ-state? curr-astate succ-term config)
  [((abstract-state: curr-term in _ _ _)
    _
    (configuration: re _ stack-map _ tr-map _ val->bits))
   (match curr-term
     ((token-case _ looks cnsqs)
      (let ((l (required-lookahead looks cnsqs succ-term val->bits)))
        ((lattice-lte? avalue-bounded-lattice) l (env-get tr-map curr-term))))
     ((get-token _)
      (non-empty-input? in))
     ((state-case _ var looks cnsqs)
      (let ((l (required-lookahead looks cnsqs succ-term val->bits))
            (aval (env-get re var)))
        ((lattice-lte? avalue-bounded-lattice) l aval)))
     (_ #t))])

;; matching-lookahead : [U [ListOf State] [ListOf Symbol]]
;;                      [ListOf Term-Seq*]
;;                      [U Term Term*]
;;                      AValue
;;                      [MutableHash Value Natural]
;;                      ->
;;                      AValue
;;
;; Returns the lookahead that matches the given branch, indicated by i. If the
;; branch is guarded by the else lookahead, base is used.
(define (matching-lookahead looks cnsqs t base val->bits)
  (let ((res (for/first ([l looks]
                         [c cnsqs]
                         #:when (equal? (first c) t))
               (or (and l (value->avalue l val->bits)) base))))
    (unless res
      (error 'matching-lookahead
             "no csnqs match ~v in ~v"
             t
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
