#lang racket

(require "../lattice/lattice.rkt"
         "abstract-value-data.rkt")
(provide env empty-env env-val-gte? env-get env-set env-set/list env-set/all-to
         register-environment-bounded-lattice
         register-environment-top
         register-environment-top?
         register-environment-bottom
         register-environment-bottom?)
(module+ test (require rackunit))

(define avalue-join (lattice-join avalue-bounded-lattice))
(define avalue-gte? (lattice-gte? avalue-bounded-lattice))

;; an [AEnv K] is a [Hash K AValue]
(define env hash)
(define empty-env (hash))
;; env-val-gte? : [AEnv K] K AValue -> Boolean
;;
;; Determines if the value bound for k is gte? than the value provided.
(define (env-val-gte? env k new-v)
  (avalue-gte? (env-get env k) new-v))
(define (env-get env key)
  (dict-ref env key avalue-bottom))
(define (env-set env register new-avalue)
  (let ((existing-avalue (env-get env register)))
    (dict-set env register (avalue-join existing-avalue new-avalue))))
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
