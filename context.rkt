#lang racket

(require "context-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "eval-pure-rhs.rkt"
         racket/generic
         )
(provide flow-ctx
         flow-ctx-unit
         flow-across
         context-top-of-stack
         init-ctx
         initial-ctx-state
         ctx-gte?
         ctx-state-callers&summaries-count
         (all-from-out "context-data.rkt")
         )


;; RelevantSet = [MutableSet Any]
(define-syntax-rule (relevant-set-constructor x ...) (mutable-set x ...))
(define (relevant-set-add s x)
  (set-add/lattice-join! s x)
  s)
(define relevant-set/c
  (set/c any/c))

;; A CtxState is a
;;   (ctx-state [MutableHash Context RelevantSet]
;;              [MutableHash Context [MutableHash Code RelevantSet]])
(struct ctx-state (callers summaries)
        #:transparent
        #:methods gen:set
        [(define/generic generic-set-count set-count)
         (define (set-count c)
           (for/sum ([(ctx ctxs) (ctx-state-callers c)])
             (generic-set-count ctxs)))])

(define ctx-state/c
  (struct/c ctx-state
            (hash/c context/c (set/c context/c))
            (hash/c context/c (hash/c any/c relevant-set/c))))

(define (initial-ctx-state) (ctx-state (make-hash) (make-hash)))

(define (ctx-state-callers&summaries-count c)
  (list (for/sum ([(callee callers) (in-hash (ctx-state-callers c))])
          (set-count callers))
        (for/sum ([(caller exit-hash) (in-hash (ctx-state-summaries c))])
          (for/sum ([(code exits) (in-hash exit-hash)])
            (set-count exits)))))

;; get-callers : ContextState Context -> [SetOf Context]
(define (get-callers ctxstate ctx)
  (hash-ref (ctx-state-callers ctxstate) ctx
            (lambda ()
              (log-debug
               "WARNING: No callers found for context ~a in callers set:\n\n ~a\n\n"
               ctx
               (ctx-state-callers ctxstate))
              (set))))

;; uppate-callers : ContextState
;;                  Context
;;                  [SetOf Context] -> [SetOf Context]
;;                  [SetOf Context]
;;                  ->
;;                  ContextState
;;
(define (update-callers! ctxstate ctx updater default)
  (hash-update! (ctx-state-callers ctxstate) ctx updater default))

(define (add-caller! ctxstate caller callee)
  (update-callers! ctxstate
                   callee
                   (lambda (callers) (relevant-set-add callers caller))
                   (relevant-set-constructor caller)))

;; get-summaries : ContextState Context Code -> [SetOf [List State Code]]
;;
(define (get-summaries ctxstate ctx)
  (for/mutable-set-union
     (((code exit) (hash-ref (ctx-state-summaries ctxstate)
                             ctx
                             (make-hash))))
   exit))

;; update-summaries : ContextState
;;                    Context
;;                    Code
;;                    [SetOf [List State Code]] -> [SetOf [List State Code]]
;;                    [SetOf [List State Code]]
;;
(define (update-summaries! ctxstate ctx code updater default)
  (hash-update! (ctx-state-summaries ctxstate)
                ctx
                (lambda (code-hash)
                  (hash-update! code-hash
                                code
                                updater
                                default)
                  code-hash)
                (make-hash)))

(define (add-summary! ctxstate ctx code exit)
  (update-summaries! ctxstate
                     ctx
                     code
                     (lambda (s) (relevant-set-add s exit))
                     (relevant-set-constructor exit)))

;; flow-ctx :  Code
;;          -> Context State ContextState Configuration
;;          -> [Values NewCtx ContextState Configuration]
;;
(define (flow-ctx node)
  (match (pda-term-insn node)
    ((assign _ var (pop))
     (lambda (ctx sigma ctxstate configuration)
       (log-debug
        "In context, ~a\n  pop, ~a, is returning into these contexts:\n~a\n\n"
        ctx node (get-callers ctxstate ctx))
       (add-summary! ctxstate ctx node (list sigma node))
       (values (many (get-callers ctxstate ctx)) ctxstate configuration)))
    ((push _ prhs)
     (lambda (ctx sigma ctxstate configuration)
       (define-values (ctx* configuration*)
         (create-ctx node ctx sigma ctxstate configuration))
       (add-caller! ctxstate ctx ctx*)
       (values (one ctx*) ctxstate configuration*)))
    (_ (lambda (ctx _ ctxstate configuration)
         (values (none) ctxstate configuration)))))

(define flow-ctx-unit
  (lambda (ctx sigma ctxstate configuration)
    (values (none) ctxstate configuration)))

;; flow-across :  Context NewCtx ContextState Configuration
;;             -> [Values [SetOf [List State Code]] ContextState Configuration]
;;
(define (flow-across old-ctx new-ctx ctxstate configuration)
  (match new-ctx
    ;; a pop introduces many new contexts, but nothing flows across
    [(struct many (ctxs))
     (values (set) ctxstate configuration)]
    ;; other insns introduce no new contexts and nothing flows across
    [(struct none ())
     (values (set) ctxstate configuration)]
    ;; a push introduces one new context, but many things flow across
    [(struct one (ctx))
     (values (for/mutable-set ([item (get-summaries ctxstate ctx)]) (cons old-ctx item))
             ctxstate
             configuration)]))

;; create-ctx : Code Context State ContextState Configuration -> [Values Context Configuration]
;;
(define (create-ctx node old-ctx sigma callers configuration)
  (match-define (push _ prhs) (pda-term-insn node))
  (define-values (stack-value configuration*)
    (eval-pure-rhs/no-monad sigma prhs configuration))
  (values (context node stack-value) configuration*))

(define-syntax-rule (for/mutable-set (iters ...) body ...)
  (let ()
    (define result (mutable-set))
    (for (iters ...)
      (set-add! result (begin body ...)))
    result))

(define-syntax-rule (for/mutable-set-union (iters ...) body ...)
  (let ()
    (define result (mutable-set))
    (for (iters ...)
      (set-union! result (begin body ...)))
    result))
