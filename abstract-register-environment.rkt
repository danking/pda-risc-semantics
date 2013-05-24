#lang racket

(require "../../../lattice/lattice.rkt"
         "abstract-value-data.rkt")
(provide env empty-env env-get env-set env-set/list env-set/all-to
         register-environment-bounded-lattice
         register-environment-top
         register-environment-top?
         register-environment-bottom
         register-environment-bottom?)
(module+ test (require rackunit))

;; a UID is a number from the register data structure
;;
;; an ARegisterEnv is a [Hash UID AValue]
(define env hash)
(define empty-env (hash))
(define env-get hash-ref)
(define env-set hash-set)
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
