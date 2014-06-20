#lang racket

(require "../lattice/lattice.rkt"
         "abstract-value-data.rkt"
         (only-in "../pda-to-pda-risc/risc-enhanced/data.rkt" register-uid))
(provide env empty-env env-val-gte? env-val-lte? env-get
         env-refine
         env-set/all-to
         (contract-out [env-set (-> any/c any/c avalue/c any/c)]
                       [env-set/list (-> any/c any/c (listof avalue/c) any/c)])
         regenv?
         register-environment-bounded-lattice
         register-environment-top
         register-environment-top?
         register-environment-bottom
         register-environment-bottom?)
(module+ test (require rackunit))

(define avalue-join (lattice-join avalue-bounded-lattice))
(define avalue-meet (lattice-meet avalue-bounded-lattice))
(define avalue-gte? (lattice-gte? avalue-bounded-lattice))
(define avalue-lte? (lattice-lte? avalue-bounded-lattice))

(struct aenv (map hash-code)
        #:transparent
        #:methods gen:dict
        [(define (dict-ref a k [f #f])
           (vector-ref (aenv-map a) k))
         (define (dict-set a k v)
           (let ((new-mapping? (and (not (avalue-bottom? v))
                                    (avalue-bottom? (vector-ref (aenv-map a) k))))
                 (new-map (vector-copy (aenv-map a))))
             (vector-set! new-map k v)
             (aenv new-map
                   (if new-mapping?
                       (+ k (aenv-hash-code a))
                       (aenv-hash-code a)))))
         (define (dict-remove a k)
           (let ((new-map (vector-copy (aenv-map a))))
             (vector-set! new-map k avalue-bottom)
             (aenv new-map (- (aenv-hash-code a) k))))
         (define (dict-count a) (vector-length (aenv-map a)))
         (define (dict-iterate-first a)
           (if (zero? (aenv-hash-code a))
               #f
               (vector-ref (aenv-map a) 0)))
         (define (dict-iterate-next  a p)
           (if (= (add1 p) (vector-length (aenv-map a)))
               #f
               (add1 p)))
         (define (dict-iterate-key   a p) p)
         (define (dict-iterate-value a p) (vector-ref (aenv-map a) p))]
        #:methods gen:equal+hash
        [(define (equal-proc a b recur)
           (and (= (aenv-hash-code a) (aenv-hash-code b))
                (recur (aenv-map a) (aenv-map b))))
         (define (hash-proc a _) (aenv-hash-code a))
         (define (hash2-proc a _) (- (aenv-hash-code a)))])

(define (compute-aenv-hash-code vec)
  (for/sum ([(k v) vec] #:when (not (avalue-bottom? v)))
    k))
(define empty-aenv-hash-code 0)
(define default-value avalue-bottom)

;; an AEnv is a (aenv [Vector AValue] Natural)

;; env : AEnv
(define-syntax-rule (env N (ks vs) ...)
  (let ((map (make-vector N default-value)))
    (for ([k (list ks ...)]
          [v (list vs ...)])
      (vector-set! k v))
    (aenv map (compute-aenv-hash-code map))))
;; empty-env : AEnv
(define (empty-env N)
  (aenv (make-vector N default-value) empty-aenv-hash-code))

;; register-view : Register -> Natural
(define (register-view r) (sub1 (register-uid r)))


;; env-val-gte? : [AEnv K] K AValue -> Boolean
;;
;; Determines if the value bound for k is gte? than the value provided.
(define (env-val-gte? env k new-v)
  (avalue-gte? (env-get env k) new-v))
;; env-val-lte? : [AEnv K] K AValue -> Boolean
;;
;; Determines if the value bound for k is lte? than the value provided.
(define (env-val-lte? env k new-v)
  (avalue-lte? (env-get env k) new-v))
(define (env-get env key)
  (dict-ref env (register-view key) avalue-bottom))
(define (env-set env register new-avalue)
  (let ((existing-avalue (env-get env register)))
    (dict-set env (register-view register) (avalue-join existing-avalue new-avalue))))
(define (env-refine env register new-avalue)
  (let ((existing-avalue (env-get env register)))
    (dict-set env (register-view register) (avalue-meet existing-avalue new-avalue))))
(define (env-set/list env vars vals)
  (for/fold ([env env])
      ([var vars]
       [val vals])
    (env-set env var val)))
(define (env-set/all-to env vars val)
  (for/fold ([env env])
      ([var vars])
    (env-set env var val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register Environment Lattice

(define-values
  (register-environment-bounded-lattice
   register-environment-top
   register-environment-top?
   register-environment-bottom
   register-environment-bottom?)
  (make-bounded-dictionary-lattice avalue-bounded-lattice))

(define (regenv? x)
  (or (aenv? x) (register-environment-bottom? x) (register-environment-top? x)))
