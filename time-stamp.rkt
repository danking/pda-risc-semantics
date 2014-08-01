#lang racket

(require "../lattice/lattice.rkt")
(provide initial-time-stamp
         time-stamp/c
         time-stamp-bounded-lattice
         )

(define initial-time-stamp 0)

(define time-stamp/c natural-number/c)

(define time-stamp-bounded-lattice
  bounded-lattice-on-numbers)
