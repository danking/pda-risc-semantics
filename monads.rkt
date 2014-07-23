#lang racket

(require (for-syntax syntax/parse))
(provide (all-defined-out))

(struct monad (bind return creator accessor))
(struct monad-value (value m) #:transparent)

(define-syntax-rule (instantiate-monad-ops bind
                                           return
                                           creator
                                           accessor
                                           (a b) ...)
  (begin (define-syntax-rule (a . x)
           (b (bind return creator accessor) . x))
         ...))

;; a [StateMonad S X] is a [StateMonad (S -> [Values X S])]
(struct StateMonad (p))

(define-syntax (~>~ stx)
  (syntax-parse stx
    [(_ (bind:expr return:expr creator:expr accessor:expr)
        ((binding:id e:expr) (binding2:id e2:expr) ...)
        body:expr)
     (quasisyntax/loc stx
       (creator
        (lambda (config)
          #,(syntax/loc stx
              (let*-values (((binding c) ((accessor e) config))
                            ((binding2 c) ((accessor e2) c))
                            ...)
                ((accessor body) c))))))]))

(define-syntax-rule (~> (bind return creator accessor)
                      ((binding expr) (binding2 expr2) ...)
                      body ...)
  (~>~ (bind return creator accessor)
       ((binding expr) (binding2 expr2) ...) (return (begin body ...))))

(define-syntax-rule (for/set~>~ (bind return creator accessor) (sequences) body)
  (creator
   (lambda (config)
     (for/fold
         ([s (set)]
          [c config])
         (sequences)
       (define-values (x new-c) ((accessor body) c))
       (values (set-add s x) new-c)))))

(define-syntax-rule (for/list~>~ (bind return creator accessor) (sequences) body)
  (creator
   (lambda (config)
     (for/fold
         ([ls '()]
          [c config])
         (sequences)
       (define-values (x new-c) ((accessor body) c))
       (values (cons x ls) new-c)))))

(define-syntax-rule (for~>~ (bind return creator accessor)
                            (sequences ...)
                            body)
  (creator
   (lambda (config)
     (for/fold
         ([v (void)]
          [c config])
         (sequences ...)
       (define-values (ignore new-c) ((accessor body) c))
       (values (void) new-c)))))

(define-syntax-rule (mapM m f ls)
  (sequence m (map f ls)))

(define-syntax-rule (sequence (bind return creator accessor) commands)
  (creator
   (lambda (config)
     (for/fold
         ([result '()]
          [config config])
         ([command commands])
       (let-values (((x config) ((accessor command) config)))
         (values (cons x result) config))))))
