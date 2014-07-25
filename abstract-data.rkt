#lang racket

(require "../lattice/lattice.rkt"
         "../racket-utils/singleton-struct.rkt"
         "abstract-value-data.rkt"
         "abstract-register-environment.rkt"
         "time-stamp.rkt")

(provide abstract-state-tr
         abstract-state-re
         (contract-out
          [make-abstract-state (-> avalue/c time-stamp/c any/c)])
         abstract-state:
         unknown-input unknown-input?
         non-empty-input non-empty-input?
         empty-input empty-input?
         init-astate
         astate-lattice
         (all-from-out "abstract-register-environment.rkt")
         (all-from-out "abstract-value-data.rkt"))

(define (write-abstract-state t port mode)
  (let ((sexp `(astate ,(abstract-state-tr t)
                       ,(abstract-state-re t))))
    ((if (pretty-printing)
         pretty-print
         write)
     sexp
     port)))

;; astate-equal? : AState AState -> Boolean
;;
;; we must ignore label environments because they have recursive structure
;; (through the label-name, which links to join-points and go instructions)
(define astate-equal?
  (match-lambda*
    [(list (abstract-state: tr1 re1)
           (abstract-state: tr2 re2)
           recur)
     (and (recur tr1 tr2) (recur re1 re2))]))
(define (compute-astate-hash-code tr re)
  (equal-hash-code (list tr re)))

;; an AInStream is [U UnknownInput NonEmptyInput EmptyInput]
(singleton-struct unknown-input)
(singleton-struct non-empty-input)
(singleton-struct empty-input)
(define (ainstream? x) (or (unknown-input? x)
                           (non-empty-input? x)
                           (empty-input? x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lattices

(define pda-term-bounded-lattice
  bounded-flat-equal?-lattice)

(define ainputstream-bounded-lattice
  bounded-flat-equal?-lattice)

(define astate-lattice
  (pointwise-lattice make-abstract-state
    [abstract-state-tr avalue-bounded-lattice]
    [abstract-state-re time-stamp-bounded-lattice]))

;; An AState is a
;;  (abstract-state-constructor AInStream
;;                              AValue
;;                              AValue
;;                              [AEnv Register]
;;                              TimeStamp
;;                              Number)
(struct abstract-state (tr re hash-code)
        #:transparent
        #:property prop:custom-write write-abstract-state
        #:methods gen:equal+hash
        [(define equal-proc astate-equal?)
         (define (hash-proc x recur) (abstract-state-hash-code x))
         (define (hash2-proc x recur) (- (abstract-state-hash-code x)))]
        #:constructor-name abstract-state-constructor
        #:methods gen:gen:join-semi-lattice
        [(define gte? (lattice-gte? astate-lattice))
         (define join (lattice-join astate-lattice))]
        #:methods gen:gen:meet-semi-lattice
        [(define lte? (lattice-lte? astate-lattice))
         (define meet (lattice-meet astate-lattice))]
        )
;; where,
;;   - in is the input stream
;;   - st is the stack
;;   - tr is the token register
;;   - re is the register environment (besides the token register)

(define-match-expander abstract-state:
  (lambda (stx)
    (syntax-case stx ()
      [(_ elts ...)
       #'(? abstract-state?
            (app (lambda (x)
                   (list
                    (abstract-state-tr x)
                    (abstract-state-re x)))
                 (list elts ...)))])))

(define (make-abstract-state tr re)
  (abstract-state-constructor tr re (compute-astate-hash-code tr re)))

(define init-astate
  (make-abstract-state avalue-bottom initial-time-stamp))

;; a LblClosureEnv is a [MutableHash LabelName ARegisterEnv]
