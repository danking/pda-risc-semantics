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
;; Global Configuration

;; A Configuration is a
;;
;; (configuration ARegisterEnv
;;                [Hash [U Term Term*] AValue]
;;                [Hash [U Term Term*] AValue]
;;                [MutableHash Value Natural])
(struct configuration (re stack-map tr-map val->bits) #:transparent)

(define init-configuration (configuration (hash) (hash) (hash)
                                          (make-hash '((#f . 1)))))

(define/match (configuration:update-re c re)
  [((configuration: _ stack-map tr-map val->bits) _)
   (configuration re stack-map tr-map val->bits)])
(define/match (configuration:update-stack-map c k v)
  [((configuration: re stack-map tr-map val->bits) _ _)
   (configuration re (env-set stack-map k v) tr-map val->bits)])
(define/match (configuration:update-tr-map c k v)
  [((configuration: re stack-map tr-map val->bits) _ _)
   (configuration re stack-map (env-set tr-map k v) val->bits)])
(define/match (configuration:update-val->bits c val->bits)
  [((configuration: re stack-map tr-map _) _)
   (configuration re stack-map tr-map val->bits)])

;; future proof the match expander
(define-match-expander configuration:
  (lambda (stx)
    (syntax-case stx ()
      [(_ elts ...)
       #'(? configuration?
            (app (lambda (x)
                   (list
                    (configuration-re x)
                    (configuration-stack-map x)
                    (configuration-tr-map x)
                    (configuration-val->bits x)))
                 (list elts ...)))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract Semantics of PDA-RISC Programs

;; A GInsn is [U Insn Insn*]

;; successor-states/new-stack : AState AState AState Configuration
;;                              ->
;;                              [Values [SetOf AState] Configuration]
;;
(define/match (successor-states/new-stack gp push pop config)
  [(_
    (abstract-state: push-term push-in push-st push-tr push-re)
    (abstract-state: pop-term pop-in pop-st pop-tr pop-re)
    (configuration: global-re stack-map tr-map val->bits))
   (match-define (assign _ var _) (pda-term-insn pop-term))
   (let ((new-re (env-set global-re var push-st)))
     (values (for/set ((succ (pda-term-succs pop-term)))
               (make-abstract-state succ pop-in push-st pop-tr new-re))
             (configuration new-re
                            (env-set/all-to stack-map
                                            (pda-term-succs pop-term)
                                            push-st)
                            tr-map
                            val->bits)))])

(define/match (successor-states push node config)
  [(_
    (abstract-state: term in st tr re)
    (configuration: global-re stack-map tr-map val->bits))
   (for/fold ([successor-state-set (set)]
              [config config])
       ([successor-term (in-set (pda-term-succs term))]
        #:when (valid-succ-state? node successor-term val->bits))
     (let-values (((successor-state config)
                   (abstract-step node successor-term config)))
       (values (set-add successor-state-set successor-state) config)))])

(define/match (abstract-step curr succ-term config)
  [((abstract-state: term in st tr re)
    _
    (configuration: re~
                    stack-map
                    tr-map
                    val->bits))
   (define st~ (hash-ref stack-map succ-term avalue-bottom))
   (define tr~ (hash-ref tr-map succ-term avalue-bottom))

   (define joined-st (avalue-join st st~))
   (define joined-tr (avalue-join tr tr~))
   (define joined-re (re-join re re~))
   (define default-new-config
     (configuration:update-re
      (configuration:update-stack-map
       (configuration:update-tr-map config succ-term joined-tr)
       succ-term joined-st)
      joined-re))

   (define eval-prhs (curry eval-pure-rhs joined-tr re~ val->bits))
   (match (pda-term-insn term)
     [(assign _ var prhs)
      (let ((new-re (env-set joined-re var (eval-prhs prhs))))
        (values (make-abstract-state succ-term in joined-st joined-tr new-re)
                (configuration:update-re default-new-config new-re)))]
     [(state-case _ var looks cnsqs)
      (let ((new-re (env-set joined-re var (possible-lookahead looks
                                                               cnsqs
                                                               succ-term
                                                               val->bits))))
        (values (make-abstract-state succ-term in joined-st joined-tr new-re)
                (configuration:update-re default-new-config new-re)))]
     [(sem-act _ name in-vars out-vars action)
      (when (not (= (length out-vars) 1))
        (warn 'sem-act
              "currently, sem-acts with anything but exactly one argument are "
              "not supported; all arguments after the first will be ignored"))
      (let ((new-re (env-set joined-re
                             (first out-vars)
                             (value->avalue (pda-term-insn term) val->bits))))
        (values (make-abstract-state succ-term in joined-st joined-tr new-re)
                (configuration:update-re default-new-config new-re)))]
     [(go _ go-target args)
      (unless (join-point? (pda-term-insn succ-term))
        (error 'go
               "this, ~a, go form is succeded by ~a instead of a join-point"
               term succ-term))
      (match-define (join-point _ join-target params) (pda-term-insn succ-term))
      (unless (equal? go-target join-target)
        (error 'go
               (string-append "this, ~a, go form's target label, ~a, doesn't "
                              "match this join-point, ~a, form's label, ~a")
               term go-target succ-term join-target))
      (let ((new-re (env-set/list joined-re params (map eval-prhs args))))
        (values (make-abstract-state succ-term in joined-st joined-tr new-re)
                (configuration:update-re default-new-config new-re)))]
     [(token-case _ looks cnsqs)
      (let ((new-tr (avalue-join (possible-lookahead looks cnsqs succ-term val->bits)
                                 tr~)))
        (values (make-abstract-state succ-term in joined-st new-tr joined-re)
                (configuration:update-tr-map default-new-config succ-term new-tr)))]
     [(push _ prhs)
      (let ((new-st (avalue-join st~ (eval-prhs prhs))))
        (values (make-abstract-state succ-term in new-st joined-tr joined-re)
                (configuration:update-stack-map default-new-config succ-term new-st)))]
     [(drop-token _)
      (values (make-abstract-state succ-term unknown-input joined-st joined-tr joined-re)
              default-new-config)]
     [(get-token _)
      (values (make-abstract-state succ-term in joined-st avalue-top joined-re)
              (configuration:update-tr-map default-new-config succ-term avalue-top))]
     [(if-eos _ cnsq altr)
      (let ((new-in (if (eq? succ-term cnsq) empty-input non-empty-input)))
        (values (make-abstract-state succ-term new-in joined-st joined-tr joined-re)
                default-new-config))]
     [(reject _)
      (error 'reject "reject should have no succesors, has ~a" succ-term)]
     [_ (values (make-abstract-state succ-term in joined-st joined-tr joined-re)
                default-new-config)])])

(define avalue-join (lattice-join avalue-bounded-lattice))
(define re-join (lattice-join register-environment-bounded-lattice))

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
;;                     [MutableHash Value Natural]
;;                     ->
;;                     Boolean
(define/match (valid-succ-state? curr-astate succ-term val->bits)
  [((abstract-state: curr-term in st tr re) _ _)
   (match curr-term
     ((token-case _ looks cnsqs)
      (let ((l (required-lookahead looks cnsqs succ-term val->bits)))
        ((lattice-lte? avalue-bounded-lattice) l tr)))
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
