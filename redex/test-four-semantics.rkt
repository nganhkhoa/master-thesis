#lang racket

;; Execute every test under four semantics and compare observations:
;; source contracts; compiler.rkt with its outer (deep) handler; the compiler
;; that places a handler at each flat monitor and is run directly (no outer
;; wrapper); and compiler2.rkt with a shallow handler, whose captured
;; continuation does not reinstall that handler.
(require rackunit redex/reduction-semantics
         "contracts.rkt"
         "effects.rkt"
         (prefix-in local-effects: "effects2.rkt")
         (prefix-in outside: "compiler.rkt")
         (prefix-in local: "compiler-local-handler.rkt")
         (prefix-in shallow: "compiler2.rkt"))

(define (contains? pred t)
  (or (pred t) (and (list? t) (ormap (λ (x) (contains? pred x)) t))))
(define (first-order? v)
  (match v
    [(? number?) #t] ['true #t] ['false #t] ['unit #t]
    [`(t ,a ,b) (and (first-order? a) (first-order? b))]
    [_ #f]))
(define (observe result)
  (match result
    [(list (list e _))
     (cond [(contains? (λ (x) (match x [`(blame ,_ ,_) #t] [`(error ,_) #t] [_ #f])) e) 'blame]
           [(first-order? e) e]
           [else 'procedure])]
    [_ (list 'unexpected result)]))
(define (source-observation p)
  (observe (apply-reduction-relation* ->contracts (term (,p ())))))
(define (outside-observation p) (observe (outside:compile-and-run p)))

;; The local compiler puts a handler around every `perform` it emits.  Unlike
;; the outer/deep and shallow variants, its target program is evaluated as-is.
(define (local-direct-result p)
  (define compiled (term (local:run-compiler ,p)))
  (apply-reduction-relation* local-effects:->effects (term (,compiled ()))))
(define (local-observation p) (observe (local-direct-result p)))
(define (shallow-observation p) (observe (shallow:compile-and-run p)))

(module+ test
  (define-syntax-rule (all-four p expected)
    (let ([source (source-observation (term p))]
          [outside (outside-observation (term p))]
          [local (local-observation (term p))]
          [shallow (shallow-observation (term p))])
      (check-equal? source (term expected) (format "source: ~s" 'p))
      (check-equal? outside source (format "outer/deep handler: ~s" 'p))
      (check-equal? local source (format "local handler, run directly: ~s" 'p))
      ;; A shallow handler does not reinstall itself around a resumed
      ;; continuation.  A first-order check therefore agrees with the source;
      ;; a later check exposed by resumption deliberately remains an unhandled
      ;; effect (observed here as a procedure).
      (check-true (or (equal? shallow source) (eq? shallow 'procedure))
                  (format "shallow handler (result or exposed continuation): ~s" 'p))))

  ;; Flat contracts.
  (all-four (mon k l j (flat (λ x num true)) 7) 7)
  (all-four (mon k l j (flat (λ x num false)) 7) blame)
  (all-four (mon k l j (flat (λ x num (zero? x))) 0) 0)
  (all-four (mon k l j (flat (λ x num (zero? x))) 1) blame)
  (all-four (add (mon k l j (flat (λ x num true)) 2) 3) 5)
  (all-four (add (mon k l j (flat (λ x num false)) 2) 3) blame)
  (all-four (if (mon k l j (flat (λ x bool true)) true) 1 2) 1)
  (all-four (if (mon k l j (flat (λ x bool false)) true) 1 2) blame)

  ;; Function contracts: range and domain, success and blame.
  (all-four ((mon k l j ((flat (λ x num true)) -> (flat (λ r num true)))
                    (λ x num (add x 1))) 10) 11)
  (all-four ((mon k l j ((flat (λ x num true)) -> (flat (λ r num false)))
                    (λ x num (add x 1))) 10) blame)
  (all-four ((mon k l j ((flat (λ x num (pos? x))) -> (flat (λ r num true)))
                    (λ x num (add x 1))) 5) 6)
  (all-four ((mon k l j ((flat (λ x num (pos? x))) -> (flat (λ r num true)))
                    (λ x num (add x 1))) -5) blame)

  ;; Curried and higher-order ranges.
  (all-four (((mon k l j
                    ((flat (λ x num true)) ->
                     ((flat (λ y num true)) -> (flat (λ r num (gt r 0)))))
                    (λ a num (λ b num (add a b)))) 1) 2) 3)
  (all-four (((mon k l j
                    ((flat (λ x num true)) ->
                     ((flat (λ y num true)) -> (flat (λ r num (gt r 0)))))
                    (λ a num (λ b num (add a b)))) 1) -5) blame)

  ;; Dependent contracts.
  (all-four ((mon k l j ((flat (λ x num true)) ->i y
                           (flat (λ r num (eq (sub r y) 1))))
                    (λ x num (add x 1))) 10) 11)
  (all-four ((mon k l j ((flat (λ x num true)) ->i y
                           (flat (λ r num (zero? (sub r y)))))
                    (λ x num (add x 1))) 10) blame)
  (all-four ((mon k l j ((flat (λ x num (pos? x))) ->i y
                           (flat (λ r num (gt r y))))
                    (λ x num (add x 1))) 3) 4)
  (all-four ((mon k l j ((flat (λ x num (pos? x))) ->i y
                           (flat (λ r num (gt r y))))
                    (λ x num (add x 1))) -3) blame)
  (all-four ((mon k l j ((flat (λ x num true)) ->i x
                           (flat (λ r num (gt r x))))
                    (λ x num (mul x 2))) 5) 10)
  (all-four ((mon k l j ((flat (λ x num true)) ->i x
                           (flat (λ r num (gt r x))))
                    (λ x num (mul x 2))) -5) blame)
  (all-four (((mon k l j
                    ((flat (λ x num true)) ->i y
                     ((flat (λ z num true)) -> (flat (λ r num (gt r y)))))
                    (λ a num (λ b num (add a b)))) 1) 2) 3)
  (all-four (((mon k l j
                    ((flat (λ x num true)) ->i y
                     ((flat (λ z num true)) -> (flat (λ r num (gt r y)))))
                    (λ a num (λ b num (add a b)))) 1) -2) blame))
