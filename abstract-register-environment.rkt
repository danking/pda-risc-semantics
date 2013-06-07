#lang racket

(require "../lattice/lattice.rkt"
         "abstract-value-data.rkt")
(provide env empty-env env-get env-set env-set/list env-set/all-to
         register-environment-bounded-lattice
         register-environment-top
         register-environment-top?
         register-environment-bottom
         register-environment-bottom?)
(module+ test (require rackunit))

(define avalue-join (lattice-join avalue-bounded-lattice))

;; an ARegisterEnv is a [Hash Any AValue]
(define env hash)
(define empty-env (hash))
(define (env-get env key [default (lambda ()
                                    (error 'env-get
                                           "key ~a, not found in environment\n  ~a"
                                           key env))])
  (dict-ref env key default))
(define (env-set env register new-avalue)
  (let ((existing-avalue (env-get env register avalue-bottom)))
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
