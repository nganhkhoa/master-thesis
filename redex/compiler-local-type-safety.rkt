#lang racket

;; Characterize conservative (𝒞)-row typing on closed programs, not
;; runtime safety. Source types are synthesized by compile, not by a separate
;; source typing judgment. The implementation's 𝒞 operation carries the party and a pair (predicate, value), matching the proof's
;; labeled payload.
(require rackunit redex/reduction-semantics
         "effects.rkt" (prefix-in compiler: "compiler-local.rkt")
         (prefix-in deep: "compiler-local-deep.rkt"))

(define Σ-check
  (term ((𝒞 : (𝒞 -> (∀ α ((t party (t (α -> (𝒞) bool) α)) -> () α)))))))
(define (source-types e)
  (judgment-holds (compiler:compile () ,e C:τ E:e) C:τ))
(define (target-types e)
  (judgment-holds (⊢ ,Σ-check () ,e τ (𝒞)) τ))

(module+ test
  (define cases
   (list
    ;; Closed programs, including results of different source types.
    (list (term 7) (term num) (list (term num)))
    (list (term (if true 1 2)) (term num) (list (term num)))
    (list (term (t 1 true)) (term (t num bool)) (list (term (t num bool))))
    (list (term ((λ x num (add x 1)) 2)) (term num) (list (term num)))
    (list (term (λ x num (add x 1))) (term (num -> num))
          (list (term (num -> (𝒞) num))))
    ;; Passing and failing checks are both statically well typed.
    (list (term (mon k l j (flat (λ x num (pos? x))) 7)) (term num) (list (term num)))
    (list (term (mon k l j (flat (λ x num (pos? x))) -1)) (term num) (list (term num)))
    (list (term (mon k l j (t (flat (λ x num (pos? x)))
                              (flat (λ b bool b))) (t 1 true)))
          (term (t num bool)) (list (term (t num bool))))
    (list (term (μ x num x)) (term num) (list (term num)))
))
  ;; The shared checker currently rejects these nested generated frames.
  ;; T-{S,D}-Handle checks the body under (𝒞 𝒞); recursive handler
  ;; checking is syntactically sensitive to that duplicate row.  These are
  ;; expected checker failures, not evidence that the translations typecheck.
  (define nested-checker-failures
   (list
    ;; Applied functions with numeric and Boolean domains/ranges.
    (list (term ((mon k l j ((flat (λ x num (pos? x))) ->
                             (flat (λ y num (gt y 0))))
                      (λ x num (add x 1))) 3)) (term num) (list (term num)))
    (list (term ((mon k l j ((flat (λ b bool b)) ->
                             (flat (λ n num (zero? n))))
                      (λ b bool (if b 0 1))) false)) (term num) (list (term num)))
    (list (term (mon k l j ((flat (λ n num (pos? n))) ->
                            (flat (λ b bool b)))
                     (λ n num (gt n 0)))) (term (num -> bool)) (list (term (num -> (𝒞) bool))))
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
                     (λ b bool b))) (term (bool -> bool)) (list (term (bool -> (𝒞) bool))))
    ;; A nested monitor in the payload value, not only function contracts.
    (list (term (mon outer peer site (flat (λ x num true))
                     (mon inner peer site (flat (λ x num true)) 7)))
          (term num) (list (term num)))
))
  (for ([case (in-list (append cases nested-checker-failures))]
        [expected-to-type? (in-list (append (make-list (length cases) #t)
                                            (make-list (length nested-checker-failures) #f)))])
    (match-define (list source expected-source local-target-types) case)
    (check-equal? (source-types source) (list expected-source)
                  (format "source type: ~s" source))
    (define compiled (term (compiler:run-compiler ,source)))
    (define deep-compiled (term (deep:run-compiler ,source)))
    (for ([target (in-list (list compiled deep-compiled))]
          [modality (in-list '(shallow deep))])
      (check-equal? (target-types target)
                    (if expected-to-type? local-target-types '())
                    (format "~a whole program (~a): ~s" modality
                            (if expected-to-type? "typable" "known checker failure") source)))))
