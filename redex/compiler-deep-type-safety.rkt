#lang racket

;; Characterize the compiler effect-safety theorem on closed programs, not
;; runtime safety. Source types are synthesized by compile, not by a separate
;; source typing judgment. The implementation's 𝒞 operation carries the party and a pair (predicate, value), matching the proof's
;; labeled payload.
(require rackunit redex/reduction-semantics
         "effects.rkt" (prefix-in compiler: "compiler-deep.rkt"))

(define Σ-check
  (term ((con : (𝒞 -> (∀ α ((t party (t (α -> (con) bool) α)) -> () α)))))))
(define (source-types e)
  (judgment-holds (compiler:compile () ,e C:τ E:e) C:τ))
(define (target-types e)
  (judgment-holds (⊢ ,Σ-check () ,e τ ()) τ))

;; The theorem translates source arrows to arrows with the check effect.
(define (translate-type τ)
  (match τ
    [`(,a -> ,b) `(,(translate-type a) -> (con) ,(translate-type b))]
    [`(t ,a ,b) `(t ,(translate-type a) ,(translate-type b))]
    [_ τ]))

(module+ test
  (define cases
   (list
    ;; Closed programs, including results of different source types.
    (list (term 7) (term num))
    (list (term (if true 1 2)) (term num))
    (list (term (t 1 true)) (term (t num bool)))
    (list (term ((λ x num (add x 1)) 2)) (term num))
    (list (term (λ x num (add x 1))) (term (num -> num)))
    ;; Passing and failing checks are both statically well typed.
    (list (term (mon k l j (flat (λ x num (pos? x))) 7)) (term num))
    (list (term (mon k l j (flat (λ x num (pos? x))) -1)) (term num))
    (list (term (mon k l j (t (flat (λ x num (pos? x)))
                              (flat (λ b bool b))) (t 1 true)))
          (term (t num bool)))
    ;; Applied functions with numeric and Boolean domains/ranges.
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->
                             (flat (λ y num (gt y 0))))
                      (λ x num (add x 1))) 3)) (term num))
    (list (term ((mon k l j ((flat (λ b bool b)) ->
                             (flat (λ n num (zero? n))))
                      (λ b bool (if b 0 1))) false)) (term num))
    (list (term (mon k l j ((flat (λ n num (pos? n))) ->
                            (flat (λ b bool b)))
                     (λ n num (gt n 0)))) (term (num -> bool)))
    ;; Dependent ranges actually refer to their checked arguments; the last
    ;; example uses that argument twice and checks an applied monitor.
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->i y
                             (flat (λ r num (gt r y))))
                      (λ x num (add x 1))) 3)) (term num))
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->i y
                             (flat (λ r num (eq r (add y y)))))
                      (λ x num (mul x 2))) 4)) (term num))
    (list (term (mon k l j ((flat (λ b bool true)) ->i b
                            (flat (λ r bool (or b r))))
                     (λ b bool b))) (term (bool -> bool)))
))
  (for ([case (in-list cases)])
    (match-define (list source expected-source) case)
    (check-equal? (source-types source) (list expected-source)
                  (format "source type: ~s" source))
    (define compiled (term (compiler:run-compiler ,source)))
    ;; The theorem wraps the entire compilation in a thunk and instantiates
    ;; wrap at the translated source result type. Do not append the extra
    ;; runtime application used by compile-and-run to drive function values.
    (define target-type (translate-type expected-source))
    (define wrapped
      (term ((compiler:wrap ,target-type) (λ (con) _ unit ,compiled))))
    ;; Assert the theorem's translated type, not just the existence of a derivation.
    (check-equal? (target-types wrapped) (list target-type)
                  (format "wrapped ~s; theorem expects ~s" source target-type))))
