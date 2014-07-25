#lang racket

(require "context-data.rkt"
         "../lattice/lattice.rkt"
         "../pda-to-pda-risc/risc-enhanced/data.rkt"
         "eval-pure-rhs.rkt"
         racket/generic
         )
(provide flow-ctx
         flow-across
         context-top-of-stack
         init-ctx
         initial-ctx-state
         ctx-gte?
         )


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
            (hash/c context/c (set/c (list/c any/c any/c)))))

(define initial-ctx-state (ctx-state (hash) (hash)))

;; get-callers : ContextState Context -> [SetOf Context]
(define (get-callers ctxstate ctx)
  (hash-ref (ctx-state-callers ctxstate) ctx
            (lambda ()
              (log-warning
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
(define (update-callers ctxstate ctx updater default)
  (ctx-state (hash-update (ctx-state-callers ctxstate) ctx updater default)
             (ctx-state-summaries ctxstate)))

;; get-summaries : ContextState Context -> [SetOf Code]
;;
(define (get-summaries ctxstate ctx)
  (hash-ref (ctx-state-summaries ctxstate) ctx (set)))

;; update-summaries : ContextState
;;                    Context
;;                    [SetOf [List State Code]] -> [SetOf [List State Code]]
;;                    [SetOf [List State Code]]
;;
(define (update-summaries ctxstate ctx updater default)
  (ctx-state (ctx-state-callers ctxstate)
             (hash-update (ctx-state-summaries ctxstate)
                          ctx
                          updater
                          default)))

(define (add-summary ctxstate ctx exit)
  (update-summaries ctxstate
                    ctx
                    (lambda (s) (set-add/lattice-join s exit))
                    (set exit)))

;; flow-ctx :  Code
;;          -> Context State ContextState Configuration
;;          -> [Values [SetOf Context] ContextState Configuration]
;;
(define (flow-ctx node)
  (match (pda-term-insn node)
    ((assign _ var (pop))
     (lambda (ctx sigma ctxstate configuration)
       (log-info
        "In context, ~a\n  pop, ~a, is returning into these contexts:\n~a\n\n"
        ctx node (get-callers ctxstate ctx))
       (values (get-callers ctxstate ctx)
               (add-summary ctxstate ctx (list sigma node))
               configuration)))
    ((push _ prhs)
     (lambda (ctx sigma ctxstate configuration)
       (define-values (ctx* configuration*)
         (create-ctx node ctx sigma ctxstate configuration))
       (values (set ctx*)
               (update-callers ctxstate
                               ctx*
                               (lambda (ctxs) (set-add ctxs ctx))
                               (set ctx))
               configuration*)))
    (_ (lambda (ctx _ ctxstate configuration)
         (values (set ctx) ctxstate configuration)))))

;; flow-across :  Context [SetOf Context] ContextState Configuration
;;             -> [Values [SetOf [List State Code]] ContextState Configuration]
;;
(define (flow-across old-ctx new-ctxs ctxstate configuration)
  (cond [(for/and ([new-ctx new-ctxs]) (equal? old-ctx new-ctxs))
         (values (set) ctxstate configuration)]
        [else ;; new ctx being introduced
         (values (for/set-union ([new-ctx new-ctxs])
                   (get-summaries ctxstate new-ctx))
                 ctxstate
                 configuration)]))

;; create-ctx : Code Context State ContextState Configuration -> [Values Context Configuration]
;;
(define (create-ctx node old-ctx sigma callers configuration)
  (match-define (push _ prhs) (pda-term-insn node))
  (define-values (stack-value configuration*)
    (eval-pure-rhs/no-monad sigma prhs configuration))
  (values (context node stack-value) configuration*))

(define-syntax-rule (for/set-union (iters ...) body ...)
  (for/fold
      ([s (set)])
      (iters ...)
    (set-union s (begin body ...))))
