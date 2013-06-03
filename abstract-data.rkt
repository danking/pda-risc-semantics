#lang racket

(require "../lattice/lattice.rkt"
         "../racket-utils/singleton-struct.rkt"
         "abstract-value-data.rkt"
         "abstract-register-environment.rkt")

(provide (struct-out abstract-state)
         (struct-out sem-act-val)
         unknown-input unknown-input?
         non-empty-input non-empty-input?
         empty-input empty-input?
         init-astate
         astate-bounded-lattice
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
    [(list (abstract-state term1 in1 st1 tr1 re1 le1)
           (abstract-state term2 in2 st2 tr2 re2 le2)
           recur)
     (and (recur term1 term2)
          (recur in1 in2)
          (recur st1 st2)
          (recur tr1 tr2))]))
(define astate-equal-hash-code
  (match-lambda*
    [(list (abstract-state term1 in1 st1 tr1 re1 le1) recur)
     (+ (recur term1)
        (recur in1)
        (recur st1)
        (recur tr1))]))
(define astate-equal-secondary-hash-code
  (match-lambda*
    [(list (abstract-state term1 in1 st1 tr1 re1 le1) recur)
     (+ (recur term1)
        (recur in1)
        (recur st1)
        (recur tr1))]))

;; an AInStream is [U UnknownInput NonEmptyInput EmptyInput]
(singleton-struct unknown-input)
(singleton-struct non-empty-input)
(singleton-struct empty-input)

;; An AState is a
;;  (abstract-state [U Term Term*]
;;                  AInStream
;;                  AValue
;;                  AValue
;;                  ARegisterEnv
;;                  LblClosureEnv)
(struct abstract-state (node in st tr re le)
        #:transparent
        #:property prop:custom-write write-abstract-state
        #:property prop:equal+hash (list astate-equal?
                                         astate-equal-hash-code
                                         astate-equal-secondary-hash-code))

;; where,
;;   - node is the pda-term
;;   - in is the input stream
;;   - st is the stack
;;   - tr is the token register
;;   - re is the register environment (besides the token register)
;;   - le is the label closure environment (all the values in scope when
;;     the labeled codepoint was created)
(define (init-astate node)
  (abstract-state node
                  unknown-input
                  avalue-bottom
                  avalue-bottom
                  empty-env
                  empty-env))

;; a LblClosureEnv is a [MutableHash LabelName ARegisterEnv]

(define (write-sem-act-val s port mode)
  (write `(sem-act-val ,(syntax->datum (sem-act-val-name s))
                       ,(map (lambda (a)
                               (if (syntax? a) (syntax-e a) a))
                             (sem-act-val-args s)))
         port))

;; a SemActVal is how we represent the result of a sem-act:
;;   (sem-act-val [Syntax Id] [ListOf Value])
(struct sem-act-val (name args) #:transparent
        #:property prop:custom-write write-sem-act-val)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lattices

(define pda-term-bounded-lattice
  bounded-flat-equal?-lattice)

(define ainputstream-bounded-lattice
  bounded-flat-equal?-lattice)

(define astate-bounded-lattice
  (pointwise-bounded-lattice abstract-state
    [abstract-state-node pda-term-bounded-lattice]
    [abstract-state-in ainputstream-bounded-lattice]
    [abstract-state-st avalue-bounded-lattice]
    [abstract-state-tr avalue-bounded-lattice]
    [abstract-state-re bounded-flat-eq?-lattice]
    [abstract-state-le bounded-flat-eq?-lattice]))
