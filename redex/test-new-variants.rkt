#lang racket

;; The cases from test-four-semantics.rkt, independently exercised against the
;; two new handler variants. Preserve that suite's coarse observation: blame
;; parties are intentionally ignored, and higher-order results are procedures.
(require rackunit redex/reduction-semantics
         "contracts.rkt" "effects.rkt"
         (prefix-in inner: "compiler-deep-inner.rkt")
         (prefix-in local: "compiler-local-deep.rkt"))

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
     (cond [(or (match e [`(blame ,_) #t] [_ #f])
                 (contains? (λ (x) (match x [`(blame ,_ ,_) #t] [_ #f])) e)) 'blame]
           [(first-order? e) e]
           [else 'procedure])]
    [_ (list 'unexpected result)]))
(define (source-observation p)
  (observe (apply-reduction-relation* ->contracts (term (,p ())))))
(define (inner-observation p) (observe (inner:compile-and-run p)))
(define (local-observation p) (observe (local:compile-and-run/local-deep p)))

(module+ test
  (define-syntax-rule (all-variants p expected)
    (let ([source (source-observation (term p))]
          [inner (inner-observation (term p))]
          [local (local-observation (term p))])
      (check-equal? source (term expected) (format "source: ~s" 'p))
      (check-equal? inner source (format "deep-inner: ~s" 'p))
      (check-equal? local source (format "local-deep: ~s" 'p))))

  ;; Also adapt the original suite's two sequential-check regressions.
  (all-variants (add (mon k l j (flat (λ x num true)) 2)
                     (mon k l j (flat (λ x num true)) 3)) 5)
  (all-variants (add (mon k l j (flat (λ x num true)) 2)
                     (mon k l j (flat (λ x num false)) 3)) blame)

  ;; Flat contracts.
  (all-variants (mon k l j (flat (λ x num true)) 7) 7)
  (all-variants (mon k l j (flat (λ x num false)) 7) blame)
  (all-variants (mon k l j (flat (λ x num (zero? x))) 0) 0)
  (all-variants (mon k l j (flat (λ x num (zero? x))) 1) blame)
  (all-variants (add (mon k l j (flat (λ x num true)) 2) 3) 5)
  (all-variants (add (mon k l j (flat (λ x num false)) 2) 3) blame)
  (all-variants (if (mon k l j (flat (λ x bool true)) true) 1 2) 1)
  (all-variants (if (mon k l j (flat (λ x bool false)) true) 1 2) blame)

  ;; Function contracts: range and domain, success and blame.
  (all-variants ((mon k l j ((flat (λ x num true)) -> (flat (λ r num true)))
                    (λ x num (add x 1))) 10) 11)
  (all-variants ((mon k l j ((flat (λ x num true)) -> (flat (λ r num false)))
                    (λ x num (add x 1))) 10) blame)
  (all-variants ((mon k l j ((flat (λ x num (pos? x))) -> (flat (λ r num true)))
                    (λ x num (add x 1))) 5) 6)
  (all-variants ((mon k l j ((flat (λ x num (pos? x))) -> (flat (λ r num true)))
                    (λ x num (add x 1))) -5) blame)

  ;; Curried and higher-order ranges.
  (all-variants (((mon k l j
                    ((flat (λ x num true)) ->
                     ((flat (λ y num true)) -> (flat (λ r num (gt r 0)))))
                    (λ a num (λ b num (add a b)))) 1) 2) 3)
  (all-variants (((mon k l j
                    ((flat (λ x num true)) ->
                     ((flat (λ y num true)) -> (flat (λ r num (gt r 0)))))
                    (λ a num (λ b num (add a b)))) 1) -5) blame)

  ;; Dependent contracts.
  (all-variants ((mon k l j ((flat (λ x num true)) ->i y
                           (flat (λ r num (eq (sub r y) 1))))
                    (λ x num (add x 1))) 10) 11)
  (all-variants ((mon k l j ((flat (λ x num true)) ->i y
                           (flat (λ r num (zero? (sub r y)))))
                    (λ x num (add x 1))) 10) blame)
  (all-variants ((mon k l j ((flat (λ x num (pos? x))) ->i y
                           (flat (λ r num (gt r y))))
                    (λ x num (add x 1))) 3) 4)
  (all-variants ((mon k l j ((flat (λ x num (pos? x))) ->i y
                           (flat (λ r num (gt r y))))
                    (λ x num (add x 1))) -3) blame)
  (all-variants ((mon k l j ((flat (λ x num true)) ->i x
                           (flat (λ r num (gt r x))))
                    (λ x num (mul x 2))) 5) 10)
  (all-variants ((mon k l j ((flat (λ x num true)) ->i x
                           (flat (λ r num (gt r x))))
                    (λ x num (mul x 2))) -5) blame)
  (all-variants (((mon k l j
                    ((flat (λ x num true)) ->i y
                     ((flat (λ z num true)) -> (flat (λ r num (gt r y)))))
                    (λ a num (λ b num (add a b)))) 1) 2) 3)
  (all-variants (((mon k l j
                    ((flat (λ x num true)) ->i y
                     ((flat (λ z num true)) -> (flat (λ r num (gt r y)))))
                    (λ a num (λ b num (add a b)))) 1) -2) blame))
