#lang racket

(require "abstract-register-environment.rkt"
         "../lattice/lattice.rkt")

(provide (except-out (struct-out configuration)
                     configuration-stack-time
                     configuration-tr-time)
         init-configuration
         configuration:
         configuration:update-re
         configuration:update-re/list
         configuration:fset-re/bump
         configuration:update-stack-map
         configuration:fset-stack-map
         configuration:stack-time
         configuration:update-tr-map
         configuration:fset-tr-map
         configuration:tr-time
         configuration:fset-val->bits
         configuration-time-stamp-lattice)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Global Configuration

;; A Configuration is a
;;
;; (configuration ARegisterEnv Natural
;;                [Hash [U Term Term*] AValue] [Hash [U Term Term*] Natural]
;;                [Hash [U Term Term*] AValue] [Hash [U Term Term*] Natural]
;;                [MutableHash Value Natural])
(struct configuration (re re-time
                       stack-map stack-time
                       tr-map tr-time
                       val->bits)
        #:transparent)

(define increment-time add1)
(define initial-time 0)
(define (increment-time/hash time-hash term)
  (hash-set time-hash term (add1 (hash-ref time-hash term initial-time))))

(define init-configuration (configuration (hash) initial-time
                                          (hash) (hash)
                                          (hash) (hash)
                                          (make-hash '((#f . 1)))))

(define (configuration:update-re c k v)
  (let ((re (configuration-re c)))
    (if (env-val-gte? re k v)
        c
        (configuration:fset-re/bump c (env-set re k v)))))
(define (configuration:update-re/list c ks vs)
  (let ((re (configuration-re c)))
    (if (for/and ((k ks) (v vs)) (env-val-gte? re k v))
        c
        (configuration:fset-re/bump c (env-set/list re ks vs)))))
(define/match (configuration:fset-re/bump c re)
  [((configuration: _ re-time
                    stack-map stack-time
                    tr-map tr-time
                    val->bits)
    _)
   (configuration re (increment-time re-time)
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])
(define (configuration:update-stack-map c k v)
  (let ((stack-map (configuration-stack-map c))
        (stack-time (configuration-stack-time c)))
   (if (env-val-gte? stack-map k v)
       c
       (configuration:fset-stack-map c
                                     (env-set stack-map k v)
                                     (increment-time/hash stack-time k)))))
(define/match (configuration:fset-stack-map c stack-map stack-time)
  [((configuration: re re-time
                    _ _
                    tr-map tr-time
                    val->bits)
    _ _)
   (configuration re re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])
(define (configuration:stack-time c k)
  (hash-ref (configuration-stack-time c) k initial-time))
(define (configuration:update-tr-map c k v)
  (let ((tr-map (configuration-tr-map c))
        (tr-time (configuration-tr-time c)))
    (if (env-val-gte? tr-map k v)
        c
        (configuration:fset-tr-map c
                                   (env-set tr-map k v)
                                   (increment-time/hash tr-time k)))))
(define/match (configuration:fset-tr-map c tr-map tr-time)
  [((configuration: re re-time
                    stack-map stack-time
                    _ _
                    val->bits)
    _ _)
   (configuration re re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])
(define (configuration:tr-time c k)
  (hash-ref (configuration-tr-time c) k initial-time))
(define/match (configuration:fset-val->bits c val->bits)
  [((configuration: re re-time
                    stack-map stack-time
                    tr-map tr-time
                    _)
    _)
   (configuration re re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])

;; future proof the match expander
(define-match-expander configuration:
  (lambda (stx)
    (syntax-case stx ()
      [(_ elts ...)
       #'(? configuration?
            (app (lambda (x)
                   (list
                    (configuration-re x)
                    (configuration-re-time x)
                    (configuration-stack-map x)
                    (configuration-stack-time x)
                    (configuration-tr-map x)
                    (configuration-tr-time x)
                    (configuration-val->bits x)))
                 (list elts ...)))])))


(define configuration-time-stamp-lattice lattice-on-numbers)
