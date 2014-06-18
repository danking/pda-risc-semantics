#lang racket

(require "../lattice/lattice.rkt"
         "../racket-utils/singleton-struct.rkt"
         ;; hack around pda-risc-enh confusion
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt"
                  state-id
                  state?
                  sem-act?
                  sem-act-name
                  sem-act-retvars))
(provide avalue-bounded-lattice
         avalue-top avalue-top? avalue?
         avalue-bottom avalue-bottom?
         ;; hack around pda-risc-enh confusion
         (struct-out state-value)
         state->state-value
         value->avalue
         avalue->value-set)
(module+ test (require rackunit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; a Value is either:
;;   - StateVal
;;   - NTerm
;;   - SemActVal
;;   - Token
;;   - UnknownInput
;;   - Bottom

;; an AValue is a [U [SetOf Value] AValueTop]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Semantic Action Values
;;
;; a SemActVal is how we represent the result of a sem-act:
;;   (sem-act-val [Syntax Id] [ListOf Value])
(define (write-sem-act-val s port mode)
  (write `(sem-act-val ,(syntax->datum (sem-act-val-name s))
                       ,(map (lambda (a)
                               (if (syntax? a) (syntax-e a) a))
                             (sem-act-val-args s)))
         port))

(struct sem-act-val (name args) #:transparent
        #:property prop:custom-write write-sem-act-val)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; State Values
;;
;; Until the PDA-RISC-ENH stuff is more sensible, let's avoid depending on
;; anything more than we must. Use state-value instead of state
(struct state-value (id) #:transparent)

(define (state->state-value s)
  (state-value (syntax->datum (state-id s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Converting between Values and AValues
;;
;; an AValue is a [SetOf Value]
;;
;; value->avalue : Value -> AValue
(define (value->avalue v)
  (cond [(state? v)
         (set (syntax->datum (state-id v)))]
        [(syntax? v) ;; v is a token from a token-case term
         (set (syntax->datum v))]
        [(sem-act? v)
         (set (syntax->datum (sem-act-name v)))]
        [else (set v)]))

;; avalue->value-set : AValue [MutableHash Value Natural] -> [SetOf Value]
;;
;; This is an ineffecient procedure to convert an avalue bit-string back into a
;; set of values. It should only be used for deubgging purposes.
(define (avalue->value-set desired-avalue val->bits)
  (let loop ((bitstring desired-avalue)
             (power-to-raise-to 0)
             (s (set)))
    (cond [(zero? bitstring) s]
          [(even? bitstring)
           (loop (arithmetic-shift bitstring -1)
                 (add1 power-to-raise-to)
                 s)]
          [else
           (loop (arithmetic-shift bitstring -1)
                 (add1 power-to-raise-to)
                 (set-add s (power-of-two->value (expt 2 power-to-raise-to) val->bits)))])))

(module+ test
  (let ((val->bits (make-hash '((a . 1) (b . 2)))))
    (check-equal? (avalue->value-set #b00 val->bits) (set))
    (check-equal? (avalue->value-set #b01 val->bits) (set 'a))
    (check-equal? (avalue->value-set #b10 val->bits) (set 'b))
    (check-equal? (avalue->value-set #b11 val->bits) (set 'a 'b))))

;; power-of-two->value : Natural [MutableHash Value Natural] -> Value
;;
;; Given a power of two, it loops through the key-value pairs in the hash to
;; find the Value associated with the given power of two.
;;
;; NB: This is not fast; only use it for debugging.
(define (power-of-two->value desired-power-of-two val->bits)
  (or (for/first (((value power-of-two) (in-hash val->bits))
                  #:when (= power-of-two desired-power-of-two))
        value)
      (error 'power-of-two->value
             "the power-of-two, 2^~a, does not appear in the mapping ~a"
             (/ (log desired-power-of-two) (log 2))
             val->bits)))

(module+ test
  (let ((val->bits (make-hash '((a . 1) (b . 2)))))
    (check-equal? (power-of-two->value 1 val->bits) 'a)
    (check-equal? (power-of-two->value 2 val->bits) 'b)
    (check-exn exn:fail?
               (lambda () (power-of-two->value 4 val->bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lattice
;;
;; AValueTop is a singleton struct representing the set of all Values. In this
;; sense it is the top element of the AValue Lattice.

(singleton-struct avalue-top #:transparent)

(define avalue-bottom 0)
(define (avalue-bottom? x)
  (and (number? x) (zero? x)))

(define (avalue? x)
  (or (number? x) (avalue-top? x)))

;; [Bounded-Lattice AValue]
;;
;; I specialize this to equal? sets so that I can use (set) as the bottom
;; element. There is no unique empty set (there's a specific one for each
;; equality predicate).
(define (unimplemented args ...)
  (error 'unimplemented ""))
;; (define set-union bitwise-ior)
(define (superset? x y) (subset? y x))
;; (define set-intersect bitwise-and)
;; (define (subset? x y)
;;   (eq? 0 (bitwise-and x (bitwise-not y))))
(define avalue-bounded-lattice
  (make-bounded-lattice/with-top&bottom (lattice set-union
                                                 superset?
                                                 set-intersect
                                                 subset?
                                                 unimplemented
                                                 unimplemented)
                                        avalue-top
                                        avalue-top?
                                        avalue-bottom
                                        avalue-bottom?))
(module+ test
  (define gte? (lattice-gte? avalue-bounded-lattice))
  (define join (lattice-join avalue-bounded-lattice))
  (define lte? (lattice-lte? avalue-bounded-lattice))
  (define meet (lattice-meet avalue-bounded-lattice))

  (define bmap (make-hash '((#f . 1))))

  (define s1 (value->avalue 'foo bmap))
  (define s2 (value->avalue 'bar bmap))
  (define s2-clone (value->avalue 'bar bmap))
  (define s1+s2 (set-union (value->avalue 'foo bmap)
                           (value->avalue 'bar bmap)))

  ;; TODO randomized testing
  (for ((test-value (list avalue-bottom
                          avalue-top
                          s1
                          s2
                          s2-clone)))
    ;; join
    (check-equal? (join test-value avalue-bottom)
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
    (check-equal? (meet test-value avalue-bottom)
                  avalue-bottom)
    ;; lte
    (check-true (lte? avalue-bottom test-value))
    (check-false (and (lte? test-value avalue-bottom)
                      (not (avalue-bottom? test-value)))))

  (check-equal? (join s1 s2)
                #b11)
  (check-equal? (meet s1 s2)
                avalue-bottom)
  (check-equal? (meet s1 s1+s2)
                s1)
  (check-equal? (join s1 s1+s2)
                s1+s2)
  (check-equal? (join s2 s2-clone)
                s2)
  (check-equal? (meet s1+s2 s2-clone)
                s2)
  (check-true (gte? s1+s2 s2-clone))
  (check-true (gte? s1+s2 s2))
  (check-true (lte? s2-clone s1+s2))
  (check-true (lte? s2 s1+s2)))
