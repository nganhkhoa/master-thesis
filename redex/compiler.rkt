#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(require "base.rkt")
(require "contracts.rkt")
(require "effects.rkt")

(define-union-language CompilerLang (C: Contracts) (E: Effects))

(define-metafunction CompilerLang
  compile : C:e -> E:e

  ;; 1. Flat Contracts
  [(compile (mon C:k C:l C:j (flat C:e_c) C:e_v))
   ((perform Check α) (t C:k (t (compile C:e_c) (compile C:e_v))))]

  ;; 2. Higher-Order Contracts
  [(compile (mon C:k C:l C:j (C:κ_1 -> C:κ_2) C:e_f))
   (λ x num
     (compile (mon C:k C:l C:j C:κ_2
                   (C:e_f (mon C:l C:k C:j C:κ_1 x)))))
   #;(where x ,(variable-not-in (term C:e_f) 'x))]

  ;; 3. Dependent Contracts (->i)
  [(compile (mon C:k C:l C:j (C:κ_1 ->i C:x C:κ_2) C:e_f))
   (λ x num
     (compile (mon C:k C:l C:j
                   (substitute C:κ_2 C:x (mon C:l C:j C:j C:κ_1 x))
                   (C:e_f (mon C:l C:k C:j C:κ_1 x)))))
   #;(where x ,(variable-not-in (term C:e_f) 'x))]

  ;; 4. Tuple Contracts
  [(compile (mon C:k C:l C:j (t C:κ_1 C:κ_2) C:e_tup))
   ((λ x num
      (t (compile (mon C:k C:l C:j C:κ_1 (injl x)))
         (compile (mon C:k C:l C:j C:κ_2 (injr x)))))
    (compile x))
   #;(where x ,(variable-not-in (term C:e_tup) 'x))]

  ;; --- Base Language Structural Recursion ---
  [(compile (λ C:x C:τ C:e))
   (λ C:x C:τ (compile C:e))]

  [(compile (C:e_1 C:e_2))
   ((compile C:e_1) (compile C:e_2))]

  [(compile (t C:e_1 C:e_2))
   (t (compile C:e_1) (compile C:e_2))]

  [(compile (injl C:e))
   (injl (compile C:e))]

  [(compile (injr C:e))
   (injr (compile C:e))]

  [(compile (+ C:e_1 C:e_2))
   (+ (compile C:e_1) (compile C:e_2))]

  [(compile (- C:e_1 C:e_2))
   (- (compile C:e_1) (compile C:e_2))]

  [(compile (if C:e_1 C:e_2 C:e_3))
   (if (compile C:e_1) (compile C:e_2) (compile C:e_3))]

  [(compile (zero? C:e))
   (zero? (compile C:e))]

  ;; --- Catch-alls for Primitives ---
  ;; Map terminals explicitly to ensure they satisfy E:e
  [(compile C:n) C:n]
  [(compile C:x) C:x]
  [(compile true) true]
  [(compile false) false])

(module+ test

  (define-term h-check
    ((Check (Λ α (λ x α (λ k α (if ((w bool) (λ _ num ((injl (injr x)) (injr (injr x)))))
                                   (k (injr (injr x)))
                                   (blame (injl x)))))))))

  (define-term wrap
    (μ w num (Λ α (λ f α ((handler h-check) f)))))

  (test-match Effects h (term h-check))
  (test-match Effects e (term wrap))

  (test-match Effects e (term (compile (λ x bool true))))

  (test-match Effects e (term (t 1 (t (λ x«19» num true) x))))
  (test-match CompilerLang E:e (term ((perform Check α) (t 1 (t (λ x«19» num true) x)))))

  ;; (require redex/gui)
  ;; (reduction-steps-cutoff 100)
  ;; (traces ->effects* (term ((wrap num)
  ;;                  (λ _ unit (compile
  ;;                               ((mon k l j
  ;;                                     ((flat (λ x num true)) -> (flat (λ x num false)))
  ;;                                     (λ x num (+ x 1)))
  ;;                                10))))))

  (test-->> ->effects*
            (term ((wrap num)
                   (λ _ unit (compile
                                ((mon k l j
                                      ((flat (λ x num true)) -> (flat (λ x num true)))
                                      (λ x num (+ x 1)))
                                 10)))))
            (term 11))

  (test-->> ->effects*
            (term ((wrap num)
                   (λ _ unit (compile
                                ((mon k l j
                                      ((flat (λ x num true)) -> (flat (λ x num false)))
                                      (λ x num (+ x 1)))
                                 10)))))
            (term (blame k)))
)
