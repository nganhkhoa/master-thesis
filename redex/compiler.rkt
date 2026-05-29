#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

;; (require "base.rkt")
(require "contracts.rkt")
(require "effects.rkt")

(define-union-language CompilerLang (C: Contracts) (E: Effects))

(define-metafunction CompilerLang
  extend : C:Γ C:x C:τ -> C:Γ
  [(extend ((C:x_1 C:τ_1) ...) C:x C:τ)
   ((C:x C:τ) (C:x_1 C:τ_1) ...)])

(define-metafunction CompilerLang
  lookup : C:Γ C:x -> C:τ
  [(lookup ((C:x_1 C:τ_1) ... (C:x C:τ) (C:x_2 C:τ_2) ...) C:x) C:τ])

(define-metafunction CompilerLang
  op-type : C:o -> ((C:τ ...) C:τ)
  [(op-type add) ((num num) num)]
  [(op-type sub) ((num num) num)]
  [(op-type mul) ((num num) num)]
  [(op-type div) ((num num) num)]

  [(op-type not)  ((bool) bool)]
  [(op-type and)  ((bool bool) bool)]
  [(op-type or)   ((bool bool) bool)]

  [(op-type pos?)   ((num) bool)]
  [(op-type neg?)   ((num) bool)]
  [(op-type zero?)  ((num) bool)]

  [(op-type lt)   ((num num) bool)]
  [(op-type lte)  ((num num) bool)]
  [(op-type gt)   ((num num) bool)]
  [(op-type gte)  ((num num) bool)]
  [(op-type eq)   ((num num) bool)]
  [(op-type neq)  ((num num) bool)])

(define-judgment-form CompilerLang
  #:mode (compile I I O O)
  #:contract (compile C:Γ C:e C:τ E:e)

  [(where C:τ (lookup C:Γ C:x))
   (where E:x ,(term C:x))
   ---------------------------- "C-VAR"
   (compile C:Γ C:x C:τ E:x)]

  [-------------------------- "C-NUM"
   (compile C:Γ C:n num C:n)]

  [--------------------------- "C-BOOL"
   (compile C:Γ C:b bool C:b)]

  [----------------------------- "C-UNIT"
   (compile C:Γ unit unit unit)]

  ;; [(where E:loc ,(term C:loc))
  ;;  ------------------------------------ "C-LOC"
  ;;  (compile C:Γ C:loc (ref τ) E:loc)]

  [(where C:Γ_new (extend C:Γ C:x C:τ_1))
   (compile C:Γ_new C:e C:τ_2 E:e_body)
   (where E:x ,(term C:x))
   ------------------------------------------------------------------------ "C-Lambda"
   (compile C:Γ (λ C:x C:τ_1 C:e) (C:τ_1 -> C:τ_2) (λ E:x C:τ_1 E:e_body))]

  [(where C:Γ_new (extend C:Γ C:x C:τ))
   (compile C:Γ_new C:e C:τ E:e_body)
   (where E:x ,(term C:x))
   ------------------------------------------------------------------------ "C-Fix"
   (compile C:Γ (μ C:x C:τ C:e) C:τ (μ E:x C:τ E:e_body))]

  [(compile C:Γ C:e_1 C:τ_1 E:e_1)
   (compile C:Γ C:e_2 C:τ_2 E:e_2)
   -------------------------------------------------------------- "C-Tuple"
   (compile C:Γ (t C:e_1 C:e_2) (t C:τ_1 C:τ_2) (t E:e_1 E:e_2))]

  [(compile C:Γ C:e (t C:τ_1 C:τ_2) E:e)
   ------------------------------------------ "C-Inj-Left"
   (compile C:Γ (injl C:e) C:τ_1 (injl E:e))]

  [(compile C:Γ C:e (t C:τ_1 C:τ_2) E:e)
   ------------------------------------------ "C-Inj-Right"
   (compile C:Γ (injr C:e) C:τ_2 (injr E:e))]

  [(compile C:Γ C:e_1 bool E:e_1)
   (compile C:Γ C:e_2 C:τ E:e_2)
   (compile C:Γ C:e_3 C:τ E:e_3)
   ---------------------------------------------------------------- "C-If"
   (compile C:Γ (if C:e_1 C:e_2 C:e_3) C:τ (if E:e_1 E:e_2 E:e_3))]

  [(where ((C:τ_arg ...) C:τ_out) (op-type C:o))
   (compile C:Γ C:e C:τ_arg E:e) ...
   (where E:o ,(term C:o))
   -------------------------------------------------- "C-Delta"
   (compile C:Γ (C:o C:e ...) C:τ_out (E:o E:e ...))]

  [(compile C:Γ C:e_1 (C:τ_1 -> C:τ_2) E:e_1)
   (compile C:Γ C:e_2 C:τ_1 E:e_2)
   ------------------------------------------------ "C-App"
   (compile C:Γ (C:e_1 C:e_2) C:τ_2 (E:e_1 E:e_2))]

  [(compile C:Γ C:e_1 (C:τ -> bool) E:e_1)
   (compile C:Γ C:e_2 C:τ E:e_2)
   ----------------------------------------------------- "C-Mon-Flat"
   (compile C:Γ (mon C:k C:l C:j (flat C:e_1) C:e_2) C:τ
            ((perform 𝒞 C:τ) (t E:e_1 E:e_2)))]

  [(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled)
   (where C:x ,(variable-not-in (term (C:Γ C:e)) 'x))
   (where C:Γ_new (extend C:Γ C:x C:τ_1))

   (compile C:Γ_new (mon C:l C:k C:j C:κ_1 C:x) C:τ_1 E:e_1)
   (compile C:Γ_new (mon C:k C:l C:j C:κ_2 (C:e C:x)) C:τ_2 E:e_2)
   (where E:e_3 (substitute E:e_2 C:x E:e_1))
   --------------------------------------------------------------- "C-Mon-Func"
   (compile C:Γ
            (mon C:k C:l C:j (C:κ_1 -> C:κ_2) C:e)
            (C:τ_1 -> C:τ_2)
            (λ C:x C:τ_1 E:e_3))]

  [(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled)
   (where (C:x C:x_κ) ,(variables-not-in (term (C:Γ C:e C:κ_2)) '(x x_k)))
   (where C:Γ_0 (extend C:Γ C:x C:τ_1))
   (where C:Γ_new (extend C:Γ_0 C:x_κ C:τ_1))

   (compile C:Γ_new (mon C:l C:k C:j C:κ_1 C:x) C:τ_1 E:e_1)
   (compile C:Γ_new (mon C:l C:j C:j C:κ_1 C:x) C:τ_1 E:e_2)
   (where C:κ_3 (substitute C:κ_2 C:x_arg C:x_κ))

   (compile C:Γ_new (mon C:k C:l C:j C:κ_3 (C:e C:x)) C:τ_2 E:e_3)
   (where E:e_4 (substitute E:e_3 C:x E:e_1))
   (where E:e_5 (substitute E:e_4 C:x_κ E:e_2))
   ----------------------------------------------------------------------- "C-Mon-Dep"
   (compile C:Γ
            (mon C:k C:l C:j (C:κ_1 ->i C:x_arg C:κ_2) C:e)
            (C:τ_1 -> C:τ_2)
            (λ C:x C:τ_1 E:e_5))]

  [(compile C:Γ (mon C:k C:l C:j C:κ_1 C:v_1) C:τ E:e_3)
   (compile C:Γ (mon C:k C:l C:j C:κ_2 C:v_2) C:τ E:e_4)
   ------------------------------------------------------------------ "C-Mon-Tuple"
   (compile C:Γ
            (mon C:k C:l C:j (tuple C:κ_1 C:κ_2) (tuple C:v_1 C:v_2))
            C:τ
            (tuple E:e_3 E:e_4))]
)

(define-metafunction CompilerLang
  run-compiler : C:e -> E:e

  [(run-compiler C:e_in) E:e_out
   (where (E:e_out E:e_extra ...) ,(judgment-holds (compile () C:e_in C:τ E:e_target) E:e_target))
   (side-condition (= (length (term (E:e_out E:e_extra ...))) 1))])

(define-metafunction CompilerLang
  run-type : C:e -> C:τ

  [(run-type C:e_in) C:τ_out
   (where (C:τ_out C:τ_extra ...) ,(judgment-holds (compile () C:e_in C:τ E:e_target) C:τ))
   (side-condition (= (length (term (C:τ_out C:τ_extra ...))) 1))])

(define-syntax-rule (compile-expect source-ast expected-ast)
  (test-equal (alpha-equivalent? CompilerLang
                                 (term (run-compiler source-ast))
                                 (term expected-ast))
              #t))


(define-term effcheck 𝒞)

(module+ test
  (compile-expect 1 1)

  (compile-expect true true)

  (compile-expect (λ x num 1)
                  (λ x num 1))

  (compile-expect (λ x num x)
                  (λ x num x))

  (compile-expect (t (λ x num x) 1)
                  (t (λ x num x) 1))

  (compile-expect (injl (t (λ x num x) 1))
                  (injl (t (λ x num x) 1)))

  (compile-expect (add 1 2)
                  (add 1 2))

  (compile-expect (mon k l j (flat (λ x num (zero? x))) 0)
                  ((perform effcheck num) (t (λ x num (zero? x)) 0)))

  (compile-expect
    (mon k l j
         ((flat (λ x num true)) -> (flat (λ x num false)))
         (λ x num (add x 1)))
    (λ x num ((perform effcheck num)
              (t (λ x num false)
                 ((λ x num (add x 1))
                  ((perform effcheck num)
                   (t (λ x num true) x)))))))

  (compile-expect
    (mon k l j
         ((flat (λ x num true)) ->i y (flat (λ x num (lt y x))))
         (λ x num (add x 1)))
    (λ arg num ((perform effcheck num)
                (t (λ x num (lt ((perform effcheck num) (t (λ x num true) arg)) x))
                   ((λ x num (add x 1))
                    ((perform effcheck num)
                     (t (λ x num true) arg)))))))
)
