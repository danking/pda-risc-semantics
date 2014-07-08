#lang racket

(require "monadic-configuration-data.rkt")
(provide widened-env-get widened-env-put environment-ts-get)

;; [ConfigMonad AEnv]
(define widened-env-get
  (ConfigMonad-creator
   (lambda (config)
     (values (first (monadic-configuration-environment config)) config))))

;; AEnv -> [ConfigMonad Void]
(define (widened-env-put aenv)
  (ConfigMonad-creator
   (lambda (config)
     (match-define (monadic-configuration bit-hash reg-count (list _ ts)) config)
     (values (void) (monadic-configuration bit-hash reg-count (list aenv (add1 ts)))))))

;; [ConfigMonad TimeStamp]
(define environment-ts-get
  (ConfigMonad-creator
   (lambda (config)
     (values (second (monadic-configuration-environment config)) config))))
