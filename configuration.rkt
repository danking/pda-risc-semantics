#lang racket

(require "abstract-register-environment.rkt"
         "abstract-value-data.rkt"
         "../lattice/lattice.rkt")

(provide (except-out (struct-out configuration)
                     configuration-re-time
                     configuration-stack-time
                     configuration-tr-time
                     )
         init-configuration
         configuration:

         configuration:env-get
         configuration:env-set
         configuration:env-refine
         configuration:env-set/list
         configuration:join-env
         configuration:re-time

         configuration:update-stack-map
         configuration:stack-time

         configuration:update-tr-map
         configuration:tr-time

         configuration:fset-val->bits

         configuration-time-stamp-lattice
         )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Global Configuration

;; A Configuration is a
;;
;; (configuration [Hash [U Term Term*] AEnv] [Hash [U Term Term*] Natural]
;;                [Hash [U Term Term*] AValue] [Hash [U Term Term*] Natural]
;;                [Hash [U Term Term*] AValue] [Hash [U Term Term*] Natural]
;;                [MutableHash Value Natural])
(struct configuration (re-map re-time
                       stack-map stack-time
                       tr-map tr-time
                       val->bits)
        #:transparent)

(define increment-time add1)
(define initial-time 0)
(define (increment-time/hash time-hash term)
  (hash-set time-hash term (add1 (hash-ref time-hash term initial-time))))

(define (init-configuration node)
  (configuration (hash node empty-env) (hash node initial-time)
                 (hash node avalue-bottom) (hash node initial-time)
                 (hash node avalue-bottom) (hash node initial-time)
                 (make-hash '((#f . 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register Environment

(define (configuration:env-get c term var)
  (env-get (hash-ref (configuration-re-map c) term empty-env)
           var))

(define (configuration:env-set c term reg v)
  (define (new-info? re)
    (not (env-val-gte? re reg v)))
  (define (updater re)
    (env-set re reg v))

  (configuration:update-re-map c new-info? updater term))

(define (configuration:env-refine c term reg v)
  (define (new-info? re)
    (not (env-val-lte? re reg v)))
  (define (updater re)
    (env-refine re reg v))

  (configuration:update-re-map c new-info? updater term))

(define (configuration:env-set/list c term regs vals)
  (define (new-info? re)
    (not (for/and ((reg regs) (val vals))
           (env-val-gte? re reg val))))
  (define (updater re)
    (env-set/list re regs vals))

  (configuration:update-re-map c new-info? updater term))

(define (configuration:join-env c term new-re)
  (define (new-info? re)
    (reg-env-gte? new-re re))
  (define (updater re)
    (reg-env-join new-re re))

  (configuration:update-re-map c new-info? updater term))

(define reg-env-join (lattice-join register-environment-bounded-lattice))
(define reg-env-gte? (lattice-gte? register-environment-bounded-lattice))

(define (configuration:update-re-map c new-info? updater term)
  (let ((re-map (configuration-re-map c))
        (re-time (configuration-re-time c)))
   (if (or (not (hash-has-key? re-map term))
           (new-info? (hash-ref re-map term)))
       (configuration:fset-re-map c
                                  (hash-set re-map
                                            term
                                            (updater (hash-ref re-map
                                                               term
                                                               empty-env)))
                                  (increment-time/hash re-time term))
       c)))
(define/match (configuration:fset-re-map c re-map re-time)
  [((configuration: _ _
                    stack-map stack-time
                    tr-map tr-time
                    val->bits)
    _ _)
   (configuration re-map re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])

(define (configuration:re-time c k)
  (hash-ref (configuration-re-time c) k initial-time))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stacks

(define (configuration:update-stack-map c k v)
  (let ((stack-map (configuration-stack-map c))
        (stack-time (configuration-stack-time c)))
    (if (and (hash-has-key? stack-map k)
             (env-val-gte? stack-map k v))
        c
        (configuration:fset-stack-map c
                                      (env-set stack-map k v)
                                      (increment-time/hash stack-time k)))))
(define/match (configuration:fset-stack-map c stack-map stack-time)
  [((configuration: re-map re-time
                    _ _
                    tr-map tr-time
                    val->bits)
    _ _)
   (configuration re-map re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])
(define (configuration:stack-time c k)
  (hash-ref (configuration-stack-time c) k initial-time))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Token Registers

(define (configuration:update-tr-map c k v)
  (let ((tr-map (configuration-tr-map c))
        (tr-time (configuration-tr-time c)))
    (if (and (hash-has-key? tr-map k)
             (env-val-gte? tr-map k v))
        c
        (configuration:fset-tr-map c
                                   (env-set tr-map k v)
                                   (increment-time/hash tr-time k)))))
(define/match (configuration:fset-tr-map c tr-map tr-time)
  [((configuration: re-map re-time
                    stack-map stack-time
                    _ _
                    val->bits)
    _ _)
   (configuration re-map re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])
(define (configuration:tr-time c k)
  (hash-ref (configuration-tr-time c) k initial-time))
(define/match (configuration:fset-val->bits c val->bits)
  [((configuration: re-map re-time
                    stack-map stack-time
                    tr-map tr-time
                    _)
    _)
   (configuration re-map re-time
                  stack-map stack-time
                  tr-map tr-time
                  val->bits)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; future proof the match expander
(define-match-expander configuration:
  (lambda (stx)
    (syntax-case stx ()
      [(_ elts ...)
       #'(? configuration?
            (app (lambda (x)
                   (list
                    (configuration-re-map x)
                    (configuration-re-time x)
                    (configuration-stack-map x)
                    (configuration-stack-time x)
                    (configuration-tr-map x)
                    (configuration-tr-time x)
                    (configuration-val->bits x)))
                 (list elts ...)))])))


(define configuration-time-stamp-lattice lattice-on-numbers)
