#lang racket

(require "../lattice/lattice.rkt"
         "../racket-utils/singleton-struct.rkt"
         "abstract-value-data.rkt"
         "abstract-register-environment.rkt")

(provide abstract-state-in
         abstract-state-st
         abstract-state-tr
         abstract-state-re
         make-abstract-state
         abstract-state:
         unknown-input unknown-input?
         non-empty-input non-empty-input?
         empty-input empty-input?
         init-astate
         astate-lattice
         (all-from-out "abstract-register-environment.rkt")
         (all-from-out "abstract-value-data.rkt"))

(define (write-abstract-state t port mode)
  (let ((sexp `(astate ,(abstract-state-in t)
                       ,(abstract-state-st t)
                       ,(abstract-state-tr t)
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
    [(list (abstract-state: in1 st1 tr1 re1)
           (abstract-state: in2 st2 tr2 re2)
           recur)
     (and (recur in1 in2)
          (recur st1 st2)
          (recur tr1 tr2)
          (recur re1 re2))]))
(define (compute-astate-hash-code in st tr re)
  (equal-hash-code (list in st tr re)))

;; an AInStream is [U UnknownInput NonEmptyInput EmptyInput]
(singleton-struct unknown-input)
(singleton-struct non-empty-input)
(singleton-struct empty-input)

;; An AState is a
;;  (abstract-state-constructor AInStream
;;                              AValue
;;                              AValue
;;                              [AEnv Register]
;;                              Number
(struct abstract-state (in st tr re hash-code)
        #:transparent
        #:property prop:custom-write write-abstract-state
        #:methods gen:equal+hash
        [(define equal-proc astate-equal?)
         (define (hash-proc x recur) (abstract-state-hash-code x))
         (define (hash2-proc x recur) (- (abstract-state-hash-code x)))]
        #:constructor-name abstract-state-constructor)
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
                    (abstract-state-in x)
                    (abstract-state-st x)
                    (abstract-state-tr x)
                    (abstract-state-re x)))
                 (list elts ...)))])))

(define (make-abstract-state in st tr re)
  (abstract-state-constructor in st tr re
                              (compute-astate-hash-code in st tr re)))

(define init-astate
  (make-abstract-state unknown-input avalue-bottom avalue-bottom (hash)))

;; a LblClosureEnv is a [MutableHash LabelName ARegisterEnv]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lattices

(define pda-term-bounded-lattice
  bounded-flat-equal?-lattice)

(define ainputstream-bounded-lattice
  bounded-flat-equal?-lattice)

(define astate-lattice
  (pointwise-lattice make-abstract-state
    [abstract-state-in ainputstream-bounded-lattice]
    [abstract-state-st avalue-bounded-lattice]
    [abstract-state-tr avalue-bounded-lattice]
    [abstract-state-re register-environment-bounded-lattice]))
