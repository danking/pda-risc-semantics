#lang racket

(require "../lattice/lattice.rkt"
         "../racket-utils/singleton-struct.rkt"
         ;; hack around pda-risc-enh confusion
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  state-id
                  state?))
(provide avalue-bounded-lattice
         avalue-top avalue-top? avalue?
         avalue-bottom avalue-bottom?
         ;; hack around pda-risc-enh confusion
         (struct-out state-value)
         state->state-value
         value->avalue)
(module+ test (require rackunit))

;; a Value is either:
;;   - StateVal
;;   - NTerm
;;   - SemActVal
;;   - Token
;;   - UnknownInput
;;   - Bottom

;; an AValue is a [U [SetOf Value] AValueTop]

;; Until the PDA-RISC-ENH stuff is more sensible, let's avoid depending on
;; anything more than we must. Use state-value instead of state
(struct state-value (id) #:transparent)

(define (state->state-value s)
  (state-value (syntax->datum (state-id s))))

;; an AValue is a [SetOf Value]
(define (value->avalue v)
  (cond [(state? v) ;; (set (state->state-value v))
         avalue-top]
        [(syntax? v) ;; v is a token from a token-case term
         ;; (set (syntax->datum v))
         avalue-top]
        [else (set v)]))

;; AValueTop is a singleton struct representing the set of all Values. In this
;; sense it is the top element of the AValue Lattice.

(define (unimplemented args ...)
  (error 'unimplemented ""))

(define (superset? x y)
  (subset? y x))

(singleton-struct avalue-top #:transparent)

(define avalue-bottom (set))
(define (avalue-bottom? x)
  (and (set? x) (set-empty? x)))

(define (avalue? x)
  (or (set? x) (avalue-top? x)))

;; [Bounded-Lattice AValue]
;;
;; I specialize this to equal? sets so that I can use (set) as the bottom
;; element. There is no unique empty set (there's a specific one for each
;; equality predicate).
(define avalue-bounded-lattice
  (make-bounded-lattice/with-top&bottom (lattice set-union
                                                 superset?
                                                 set-intersect
                                                 subset?
                                                 unimplemented
                                                 unimplemented)
                                        avalue-top
                                        avalue-top?
                                        (set)
                                        avalue-bottom?))
(module+ test
  (define gte? (lattice-gte? avalue-bounded-lattice))
  (define join (lattice-join avalue-bounded-lattice))
  (define lte? (lattice-lte? avalue-bounded-lattice))
  (define meet (lattice-meet avalue-bounded-lattice))

  ;; TODO randomized testing
  (for ((test-value (list (set 3 1 3)
                          (set)
                          avalue-top
                          (set 5)
                          (set (set 3) (set 5))
                          (set 'a 'b 'c)
                          (set "hi" "hello" "what?"))))
    ;; join
    (check-equal? (join test-value (set))
                  test-value)
    (check-equal? (join test-value avalue-top)
                  avalue-top)
    ;; gte
    (check-true (gte? avalue-top test-value))
    (check-false (and (gte? test-value avalue-top)
                      (not (avalue-top? test-value))))
    ;; meet
    (check-equal? (meet test-value avalue-top)
                  test-value)
    (check-equal? (meet test-value (set))
                  (set))
    ;; lte
    (check-true (lte? (set) test-value))
    (check-false (and (lte? test-value (set))
                      (not (avalue-bottom? test-value)))))

  (check-equal? (join (set 1 3) (set 5 6))
                (set 1 3 5 6))
  (check-equal? (meet (set 1 3) (set 5 6))
                (set))
  (check-equal? (meet (set 1 3 5) (set 5 6))
                (set 5)))
