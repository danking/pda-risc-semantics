#lang racket

(require "../lattice/lattice.rkt"
         "abstract-value-data.rkt")
(provide env empty-env env-get env-set! env-set/list!
         register-environment-bounded-lattice
         register-environment-top
         register-environment-top?
         register-environment-bottom
         register-environment-bottom?)
(module+ test (require rackunit))

(define avalue-join (lattice-join avalue-bounded-lattice))

;; a UID is a number from the register data structure
;;
;; an ARegisterEnv is a [MutableHash UID AValue]
(define env make-hash)
(define empty-env (make-hash))
(define env-get hash-ref)
(define (env-set! env register new-avalue)
  (let ((existing-avalue (env-get env register avalue-bottom)))
    (hash-set! env register (avalue-join existing-avalue new-avalue))))
(define (env-set/list! env vars vals)
  (for ([var vars]
        [val vals])
    (env-set! env var val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Register Environment Lattice

(define-values
  (register-environment-bounded-lattice
   register-environment-top
   register-environment-top?
   register-environment-bottom
   register-environment-bottom?)
  (make-bounded-dictionary-lattice avalue-bounded-lattice))
