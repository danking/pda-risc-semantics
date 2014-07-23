#lang racket

(require "../lattice/lattice.rkt"
         "abstract-value-data.rkt")
(provide (struct-out context)
         context/c
         init-ctx
         )

(define context-lattice
  (pointwise-lattice context
                     [context-push flat-equal?-lattice]
                     [context-top-of-stack avalue-bounded-lattice]))

(define avalue-gte? (lattice-gte? avalue-bounded-lattice))

;; (context [Maybe PDA-TERM] AValue)
(struct context (push top-of-stack)
        #:transparent
        #:methods gen:gen:join-semi-lattice
        [(define (gte? x y)
           (and (equal? (context-push x) (context-push y))
                (avalue-gte? (context-top-of-stack x) (context-top-of-stack y))))
         (define join (lattice-join context-lattice))]
        #:methods gen:gen:meet-semi-lattice
        [(define lte? (lattice-lte? context-lattice))
         (define meet (lattice-meet context-lattice))]
        )

(define context/c (struct/c context any/c avalue/c))

(define init-ctx (context #f avalue-top))
