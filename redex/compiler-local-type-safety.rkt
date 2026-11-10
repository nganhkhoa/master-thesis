#lang racket

;; Characterize the compiler effect-safety theorem on closed programs, not
;; runtime safety. Source types are synthesized by compile, not by a separate
;; source typing judgment. The implementation's 𝒞 operation carries the party and a pair (predicate, value), matching the proof's
;; labeled payload.
(require rackunit redex/reduction-semantics
         "effects.rkt" (prefix-in compiler: "compiler-local.rkt"))

(define Σ-check
  (term ((𝒞 : (𝒞 -> (∀ α ((t party (t (α -> () bool) α)) -> () α)))))))
(define (source-types e)
  (judgment-holds (compiler:compile () ,e C:τ E:e) C:τ))
(define (target-types e)
  (judgment-holds (⊢ ,Σ-check () ,e τ ()) τ))

(module+ test
  (define cases
   (list
    ;; Closed programs, including results of different source types.
    (list (term 7) (term num) (list (term num)))
    (list (term (if true 1 2)) (term num) (list (term num)))
    (list (term (t 1 true)) (term (t num bool)) (list (term (t num bool))))
    (list (term ((λ x num (add x 1)) 2)) (term num) (list (term num)))
    (list (term (λ x num (add x 1))) (term (num -> num))
          (list (term (num -> () num))))
    ;; Passing and failing checks are both statically well typed.
    (list (term (mon k l j (flat (λ x num (pos? x))) 7)) (term num) (list (term num)))
    (list (term (mon k l j (flat (λ x num (pos? x))) -1)) (term num) (list (term num)))
    (list (term (mon k l j (t (flat (λ x num (pos? x)))
                              (flat (λ b bool b))) (t 1 true)))
          (term (t num bool)) (list (term (t num bool))))
    ;; Applied functions with numeric and Boolean domains/ranges.
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->
                             (flat (λ y num (gt y 0))))
                      (λ x num (add x 1))) 3)) (term num) (list (term num)))
    (list (term ((mon k l j ((flat (λ b bool b)) ->
                             (flat (λ n num (zero? n))))
                      (λ b bool (if b 0 1))) false)) (term num) (list (term num)))
    (list (term (mon k l j ((flat (λ n num (pos? n))) ->
                            (flat (λ b bool b)))
                     (λ n num (gt n 0)))) (term (num -> bool)) (list (term (num -> () bool))))
    ;; Dependent ranges actually refer to their checked arguments; the last
    ;; example uses that argument twice and checks an applied monitor.
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->i y
                             (flat (λ r num (gt r y))))
                      (λ x num (add x 1))) 3)) (term num) (list (term num)))
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->i y
                             (flat (λ r num (eq r (add y y)))))
                      (λ x num (mul x 2))) 4)) (term num) (list (term num)))
    (list (term (mon k l j ((flat (λ b bool true)) ->i b
                            (flat (λ r bool (or b r))))
                     (λ b bool b))) (term (bool -> bool)) (list (term (bool -> () bool))))
    (list (term (μ x num x)) (term num) (list (term num)))
))
  (for ([case (in-list cases)])
    (match-define (list source expected-source local-target-types) case)
    (check-equal? (source-types source) (list expected-source)
                  (format "source type: ~s" source))
    (define compiled (term (compiler:run-compiler ,source)))
    ;; The local compiler already installs a handler at each check; unlike
    ;; the global compilers, no outer handler or thunk is added.
    (check-equal? (target-types compiled) local-target-types
                  (format "local whole program: ~s" source))))
