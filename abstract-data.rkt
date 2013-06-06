#lang racket

(require "../lattice/lattice.rkt"
         "../racket-utils/singleton-struct.rkt"
         "abstract-value-data.rkt"
         "abstract-register-environment.rkt")

(provide abstract-state-node
         abstract-state-in
         abstract-state-re
         abstract-state-st
         abstract-state-tr
         make-abstract-state/same-system
         abstract-state:
         unknown-input unknown-input?
         non-empty-input non-empty-input?
         empty-input empty-input?
         init-astate
         astate-lattice
         (all-from-out "abstract-register-environment.rkt")
         (all-from-out "abstract-value-data.rkt"))

(define (write-abstract-state t port mode)
  (let ((sexp `(astate ,(abstract-state-node t)
                       ,(abstract-state-in t)
                       ,(abstract-state-st t)
                       ,(abstract-state-tr t)
                       <#register-environment:...>)))
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
    [(list (abstract-state: term1 in1 st1 tr1 _ _ _)
           (abstract-state: term2 in2 st2 tr2 _ _ _)
           recur)
     (and (recur term1 term2)
          (recur in1 in2)
          (recur st1 st2)
          (recur tr1 tr2))]))
(define (compute-astate-hash-code node in st tr)
  (equal-hash-code (list node in st tr)))

;; an AInStream is [U UnknownInput NonEmptyInput EmptyInput]
(singleton-struct unknown-input)
(singleton-struct non-empty-input)
(singleton-struct empty-input)

;; An AState is a
;;  (abstract-state-constructor [U Term Term*]
;;                              AInStream
;;                              ARegisterEnv
;;                              LblClosureEnv
;;                              [MutableHash Value Natural]
;;                              Number
;;                              [MutableHash [U Term Term*] AValue]
;;                              [MutableHash [U Term Term*] AValue])
(struct abstract-state (node in re le val->bits hash-code stack-hash tr-hash)
        #:transparent
        #:property prop:custom-write write-abstract-state
        #:methods gen:equal+hash
        [(define equal-proc astate-equal?)
         (define (hash-proc x recur) (abstract-state-hash-code x))
         (define (hash2-proc x recur) (- (abstract-state-hash-code x)))]
        #:constructor-name abstract-state-constructor)

(define-match-expander abstract-state:
  (lambda (stx)
    (syntax-case stx ()
      [(_ elts ...)
       #'(? abstract-state?
            (app (lambda (x)
                   (list
                    (abstract-state-node x)
                    (abstract-state-in x)
                    (abstract-state-st x)
                    (abstract-state-tr x)
                    (abstract-state-re x)
                    (abstract-state-le x)
                    (abstract-state-val->bits x)))
                 (list elts ...)))])))

(define (abstract-state-st as)
  (hash-ref (abstract-state-stack-hash as) (abstract-state-node as) avalue-bottom))

(define (abstract-state-tr as)
  (hash-ref (abstract-state-tr-hash as) (abstract-state-node as) avalue-bottom))

(define (hash-set!/join bounded-lattice hash key value)
  (hash-set! hash
             key
             ((lattice-join bounded-lattice)
              (hash-ref hash
                        key
                        (bounded-lattice-bottom bounded-lattice))
              value)))

(define avalue-hash-set!/join (curry hash-set!/join avalue-bounded-lattice))

(define (make-abstract-state/same-system node in st tr existing-astate)
  (make-abstract-state node in st tr
                       (abstract-state-re existing-astate)
                       (abstract-state-le existing-astate)
                       (abstract-state-val->bits existing-astate)
                       (abstract-state-stack-hash existing-astate)
                       (abstract-state-tr-hash existing-astate)))

(define (make-abstract-state node in st tr re le val->bits stack-hash tr-hash)
  (avalue-hash-set!/join stack-hash node st)
  (avalue-hash-set!/join tr-hash node tr)
  (abstract-state-constructor node in re le val->bits
                              (compute-astate-hash-code node in st tr)
                              stack-hash
                              tr-hash))

(define (same-system? x y)
  (and (eq? (abstract-state-stack-hash x) (abstract-state-stack-hash y))
       (eq? (abstract-state-tr-hash x) (abstract-state-tr-hash y))))

;; where,
;;   - node is the pda-term
;;   - in is the input stream
;;   - st is the stack
;;   - tr is the token register
;;   - re is the register environment (besides the token register)
;;   - le is the label closure environment (all the values in scope when
;;     the labeled codepoint was created)
;;   - val->bits is the mapping from values to bits
(define (init-astate node)
  (make-abstract-state node
                       unknown-input
                       avalue-bottom
                       avalue-bottom
                       empty-env
                       empty-env
                       (make-hash '((#f . 1)))
                       (make-hash)
                       (make-hash)))

;; a LblClosureEnv is a [MutableHash LabelName ARegisterEnv]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lattices

(define pda-term-bounded-lattice
  bounded-flat-equal?-lattice)

(define ainputstream-bounded-lattice
  bounded-flat-equal?-lattice)

(define astate-lattice
  (pointwise-lattice make-abstract-state
    [abstract-state-node pda-term-bounded-lattice]
    [abstract-state-in ainputstream-bounded-lattice]
    [abstract-state-st avalue-bounded-lattice]
    [abstract-state-tr avalue-bounded-lattice]
    [abstract-state-re flat-eq?-lattice]
    [abstract-state-le flat-eq?-lattice]
    [abstract-state-val->bits flat-eq?-lattice]
    [abstract-state-stack-hash flat-eq?-lattice]
    [abstract-state-tr-hash flat-eq?-lattice]))
