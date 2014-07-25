#lang racket

(require "../lattice/lattice.rkt"
         "abstract-value-data.rkt"
         "../pda-to-pda-risc/risc-enhanced/fast-equal.rkt")
(provide (struct-out context)
         context/c
         init-ctx
         ctx-gte?
         )

(define context-lattice
  (pointwise-lattice context
                     [context-push flat-equal?-lattice]
                     [context-top-of-stack avalue-bounded-lattice]))

(define avalue-gte? (lattice-gte? avalue-bounded-lattice))

(define (ctx-gte? x y)
  (let* ((cx (context-push x))
         (cy (context-push y))
         (fcx (false? cx))
         (fcy (false? cy)))
    (and (or (and fcx fcy)
             (and (not fcx) (not fcy)
                  (fast-term-equal? cx cy)))
         (avalue-gte? (context-top-of-stack x) (context-top-of-stack y)))))

;; (context [Maybe PDA-TERM] AValue)
(struct context (push top-of-stack)
        #:transparent
        #:methods gen:gen:join-semi-lattice
        [(define gte? ctx-gte?)
         (define join (lattice-join context-lattice))]
        #:methods gen:gen:meet-semi-lattice
        [(define lte? (lattice-lte? context-lattice))
         (define meet (lattice-meet context-lattice))]
        )

(define context/c (struct/c context any/c avalue/c))

(define init-ctx (context #f avalue-top))
