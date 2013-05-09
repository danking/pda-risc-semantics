#lang racket

(provide env empty-env env-get env-set env-set/list env-set/all-to
         register-env-join)
(module+ test (require rackunit))

;; an AValue is a [SetOf Value]
;;
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

;; register-env-join : RegisterEnv RegisterEnv -> RegisterEnv
(define (register-env-join re1 re2)
  (for/fold ([new-re re1])
      ([(k v) (in-hash re2)])
    (hash-set new-re k (set-union v (hash-ref new-re k (set))))))
(module+ test
  (check-equal? (register-env-join empty-env empty-env)
                empty-env)
  (check-equal? (register-env-join empty-env (env 1 (set 'a)))
                (env 1 (set 'a)))
  (check-equal? (register-env-join (env 1 (set 'a)) empty-env)
                (env 1 (set 'a)))
  (check-equal? (register-env-join (env 1 (set 'a)) empty-env)
                (env 1 (set 'a)))
  (check-equal? (register-env-join (env 1 (set 'a)) (env 2 (set 'b)))
                (env 1 (set 'a) 2 (set 'b)))
  (check-equal? (register-env-join (env 1 (set 'a)) (env 1 (set 'b)))
                (env 1 (set 'a 'b))))
