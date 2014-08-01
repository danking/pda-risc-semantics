#lang racket
(require "abstract-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "monadic-configuration.rkt"
         "monadic-configuration-environment.rkt"
         "eval-pure-rhs.rkt"
         "context-data.rkt"
         (prefix-in monad: "monads.rkt")
         (for-syntax racket
                     racket/syntax
                     syntax/parse))

(provide compute-flow-function
         flow-function-unit
         init-astate
         abstract-state-gte?
         abstract-state-tr
         abstract-state-re
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

;; Code is [U Insn Insn*]

;; compute-flow-function :  Code
;;                       -> Context AState
;;                       -> [ConfigMonad [SetOf [List AState Code]]]
(define (compute-flow-function term)
  (define succ-terms (pda-term-succs term))
  (define insn (pda-term-insn term))

  [match insn
    [(assign _ var (pop))
     (lambda (ctx new-ctx sigma config)
       (match-define (struct many (new-ctxs)) new-ctx)
       (match-define (abstract-state: tr re) sigma)
       (run-config-monad*
        config
        (~> ((_ (env-set var (context-top-of-stack ctx)))
             (new-re environment-ts-get))
          (for*/set ([succ-term (in-set succ-terms)]
                     [new-ctx (in-set new-ctxs)])
            (list new-ctx
                  (make-abstract-state tr new-re)
                  succ-term)))))]
    [(assign _ var prhs)
     (flow-function
      (~> ((value (eval-pure-rhs tr prhs))
           (_ (env-set var value))
           (new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state tr new-re) succ-term))))]
    [(state-case _ var looks cnsqs)
     (flow-function
      (~>~ ((succ-terms+looks (for/list~>~ ([succ-term (in-set succ-terms)])
                                (~> ((lookahead (possible-lookahead looks cnsqs succ-term)))
                                  (list succ-term lookahead)))))
        (for/set~>~ ([s+l (in-list succ-terms+looks)])
          (~> ((_ (env-refine var (second s+l)))
               (new-re environment-ts-get))
            (list new-ctx (make-abstract-state tr new-re) (first s+l))))))]
    [(sem-act _ name in-vars out-vars action)
     (when (not (= (length out-vars) 1))
       (warn 'sem-act
             "currently, sem-acts with anything but exactly one argument are "
             "not supported; all arguments after the first will be ignored"))
     (flow-function
      (~> ((aval (value->avalue insn))
           (_ (env-set (first out-vars) aval))
           (new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state tr new-re) succ-term))))]
    [(go _ go-target args)
     (for ([succ-term (in-set succ-terms)])
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
     (flow-function
      (~>~ ((values (mapM (curry eval-pure-rhs tr) args)))
        (for/set~>~ ([succ-term (in-set succ-terms)])
          (~> ((_ (env-set/list (join-point-params
                                 (pda-term-insn succ-term))
                                values))
               (new-re environment-ts-get))
            (list new-ctx (make-abstract-state tr new-re) succ-term)))))]
    [(token-case _ looks cnsqs)
     ;; Here we update the token register to the predeceessors tr met with the
     ;; lookahead for this consequent, (tr ⊓ look-tr)
     (flow-function
      (~> ((succ-terms+looks (for/list~>~ ([succ-term (in-set succ-terms)])
                               (~> ((lookahead (possible-lookahead looks cnsqs succ-term)))
                                 (list succ-term lookahead))))
           (new-re environment-ts-get))
        (for/set ([s+l (in-list succ-terms+looks)])
          (list new-ctx
                (make-abstract-state (avalue-meet tr (second s+l)) new-re)
                (first s+l)))))]
    [(push _ prhs)
     ;; Here we overwrite the stack which is above joined with the
     ;; predecessor's stack. We set it to the join of what was previously there
     ;; with the new stack that we learned about from this push.
     (flow-function
      (~> ((new-st (eval-pure-rhs tr prhs))
           (new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state tr new-re) succ-term))))]
    [(drop-token _)
     (flow-function
      (~> ((new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state tr new-re) succ-term))))]
    [(get-token _)
     (flow-function
      (~> ((new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state avalue-top new-re) succ-term))))]
    [(if-eos _ cnsq altr)
     (flow-function
      (~> ((new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state tr new-re) succ-term))))]
    [(reject _)
     (unless (set-empty? succ-terms)
       (error 'reject "reject should have no succesors, has ~a" succ-terms))
     (flow-function
      (return (set)))]
    [_
     (flow-function
      (~> ((new-re environment-ts-get))
        (for/set ([succ-term (in-set succ-terms)])
          (list new-ctx (make-abstract-state tr new-re) succ-term))))]])

(define flow-function-unit
  (lambda (ctx new-ctx sigma config)
    (values (set) config)))

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
    (for/first ([l (in-list looks)]
                [c (in-list cnsqs)]
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
     (let ((variable-bindings (map (curry datum->syntax #'body) '(tr re)))
           (new-ctx (datum->syntax #'body 'new-ctx)))
       #`(match-lambda**
           [(ctx (struct one (#,new-ctx)) (abstract-state: #,@variable-bindings) config)
            (run-config-monad* config body)]
           [(ctx (struct none ()) (abstract-state: #,@variable-bindings) config)
            (let ((#,new-ctx ctx))
              (run-config-monad* config body))]))]))

