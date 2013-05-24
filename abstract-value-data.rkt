#lang racket

(require "../../../lattice/lattice.rkt")
(provide avalue-bounded-lattice)

;; an [AValue X] is a [SetOf X]

(struct avalue-lattice-top ())

;; [Bounded-Lattice [SetOf Any]]
;;
;; I specialize this to equal? sets so that I can use (set) as the bottom
;; element. There is no unique empty set (there's a specific one for each
;; equality predicate).
(define avalue-bounded-lattice
  ;; TODO avalue-lattice-top???
  (bounded-lattice set-union
                   (lambda (x y) (subset? y x))
                   set-intersect
                   subset?
                   (lambda (x y) (and (set-equal? x) (set-equal? y)))
                   (lambda (x _) (equal-hash-code x))
                   (avalue-lattice-top)
                   (set)))
