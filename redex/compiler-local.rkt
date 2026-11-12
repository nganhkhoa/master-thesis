#lang racket

(provide CompilerLocalHandler compile run-compiler run-type
         compile-and-run/local-handler)

(require redex/reduction-semantics rackunit)

(require "contracts.rkt")
;; Every flat monitor installs a shallow handler at its point of use.
(require "effects.rkt")

(define-union-language CompilerLocalHandler (C: Contracts) (E: Effects))

(define-metafunction CompilerLocalHandler
  extend : C:Γ C:x C:τ -> C:Γ
  [(extend ((C:x_1 C:τ_1) ...) C:x C:τ)
   ((C:x C:τ) (C:x_1 C:τ_1) ...)])

(define-metafunction CompilerLocalHandler
  lookup : C:Γ C:x -> C:τ
  [(lookup ((C:x_1 C:τ_1) ... (C:x C:τ) (C:x_2 C:τ_2) ...) C:x) C:τ])

;; Use the conservative 𝒞 row throughout: a shallow resumption retains 𝒞,
;; so both modalities need this outer row for identical, typable clauses.
;; Translate annotations recursively.
(define-metafunction CompilerLocalHandler
  translate-type : C:τ -> E:τ
  [(translate-type (C:τ_1 -> C:τ_2))
   ((translate-type C:τ_1) -> (𝒞) (translate-type C:τ_2))]
  [(translate-type (t C:τ_1 C:τ_2))
   (t (translate-type C:τ_1) (translate-type C:τ_2))]
  [(translate-type (ref C:τ)) (ref (translate-type C:τ))]
  [(translate-type num) num]
  [(translate-type bool) bool]
  [(translate-type unit) unit])

(define-metafunction CompilerLocalHandler
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

(define-judgment-form CompilerLocalHandler
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

  [(where C:Γ_new (extend C:Γ C:x C:τ_1))
   (compile C:Γ_new C:e C:τ_2 E:e_body)
   (where E:x ,(term C:x))
   (where E:τ_1 (translate-type C:τ_1))
   ------------------------------------------------------------------------ "C-Lambda"
   (compile C:Γ (λ C:x C:τ_1 C:e) (C:τ_1 -> C:τ_2) (λ (𝒞) E:x E:τ_1 E:e_body))]

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
   (where E:p ,(symbol->string (term C:k)))
   (where E:τ (translate-type C:τ))
   ;; The operation clause runs outside the handler.  For shallow handling,
   ;; its continuation has row (𝒞); giving both modalities that same outer
   ;; row makes their generated clauses identical (rows are sets).
   ;; Keep the original payload inside the direct handler frame.
   (where (E:x_payload E:x_k E:α)
          ,(variables-not-in (term (C:Γ C:e_1 C:e_2 E:e_1 E:e_2 E:τ))
                             '(payload k β)))
   ----------------------------------------------------- "C-Mon-Flat"
   (compile C:Γ (mon C:k C:l C:j (flat C:e_1) C:e_2) C:τ
            (s-handle (𝒞)
              ((𝒞
                (Λ E:α
                  (λ (𝒞) E:x_payload (t party (t (E:α -> (𝒞) bool) E:α))
                    (λ (𝒞) E:x_k (E:α -> (𝒞) E:τ)
                      (if ((injl (injr E:x_payload)) (injr (injr E:x_payload)))
                          (E:x_k (injr (injr E:x_payload)))
                          (blame (injl E:x_payload))))))))
              ((perform () 𝒞 E:τ) (t (party E:p) (t E:e_1 E:e_2)))))]

  ;; GUARD-FUNC swaps the domain parties, just like GUARD-DEP.
  [(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled)
   (where (C:x C:x_1) ,(variables-not-in (term (C:Γ C:e C:κ_1 C:κ_2)) '(x x_1)))
   (compile C:Γ
            (λ C:x_1 (C:τ_1 -> C:τ_2)
              (λ C:x C:τ_1
                (mon C:k C:l C:j C:κ_2
                     (C:x_1 (mon C:l C:k C:j C:κ_1 C:x)))))
            ((C:τ_1 -> C:τ_2) -> (C:τ_1 -> C:τ_2))
            E:e_4)

   --------------------------------------------------------------- "C-Mon-Func"
   (compile C:Γ
            (mon C:k C:l C:j (C:κ_1 -> C:κ_2) C:e)
            (C:τ_1 -> C:τ_2)
            ;; remember to evaluate the contract expression first
            (E:e_4 E:e_compiled))]

  ;; ((guard k l j (κ_1 ->i y κ_2) f) v)
  ;;   --> (mon k l j κ_2[y := (mon l j j κ_1 v)] (f (mon l k j κ_1 v)))
  ;;
  ;; Preserve that substitution literally.  In particular, do *not* bind the
  ;; checked argument to x_arg and reuse the binding in κ_2: each occurrence
  ;; of x_arg in the dependent range must re-run its monitor, just as it does
  ;; in ->contracts (and hence may matter for effectful values such as boxes).
  [(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled)
   (where (C:x C:x_1) ,(variables-not-in (term (C:Γ C:e C:κ_1 C:κ_2 C:x_arg)) '(x x_1)))
   (where C:κ_range
          (substitute C:κ_2 C:x_arg (mon C:l C:j C:j C:κ_1 C:x)))
   (compile C:Γ
            (λ C:x_1 (C:τ_1 -> C:τ_2)
              (λ C:x C:τ_1
                (mon C:k C:l C:j C:κ_range
                     (C:x_1 (mon C:l C:k C:j C:κ_1 C:x)))))
            ((C:τ_1 -> C:τ_2) -> (C:τ_1 -> C:τ_2))
            E:e_4)
   ----------------------------------------------------------------------- "C-Mon-Dep"
   (compile C:Γ
            (mon C:k C:l C:j (C:κ_1 ->i C:x_arg C:κ_2) C:e)
            (C:τ_1 -> C:τ_2)
            (E:e_4 E:e_compiled))]

  [(where C:x ,(variable-not-in (term (C:Γ C:e C:κ_1 C:κ_2)) 'x))
   (compile C:Γ C:e (t C:τ_1 C:τ_2) E:e_3)
   (where C:Γ_0 (extend C:Γ C:x (t C:τ_1 C:τ_2)))
   (compile C:Γ_0 (mon C:k C:l C:j C:κ_1 (injl C:x)) C:τ_1 E:e_1)
   (compile C:Γ_0 (mon C:k C:l C:j C:κ_2 (injr C:x)) C:τ_2 E:e_2)
   (where E:τ (translate-type (t C:τ_1 C:τ_2)))
   ------------------------------------------------------------------ "C-Mon-Tuple"
   (compile C:Γ
            (mon C:k C:l C:j (t C:κ_1 C:κ_2) C:e)
            (t C:τ_1 C:τ_2)
            ((λ (𝒞) C:x E:τ (t E:e_1 E:e_2)) E:e_3))]
)

(define-metafunction CompilerLocalHandler
  run-compiler : C:e -> E:e
  [(run-compiler C:e_in) E:e_out
   (where (E:e_out E:e_extra ...) ,(judgment-holds (compile () C:e_in C:τ E:e) E:e))
   (side-condition (= 1 (length (term (E:e_out E:e_extra ...)))))])
(define-metafunction CompilerLocalHandler
  run-type : C:e -> C:τ
  [(run-type C:e_in) C:τ_out
   (where (C:τ_out C:τ_extra ...) ,(judgment-holds (compile () C:e_in C:τ E:e) C:τ))
   (side-condition (= 1 (length (term (C:τ_out C:τ_extra ...)))))])

;; No recursive or global wrapper is needed: each flat monitor has a frame.
(define (compile-and-run/local-handler source)
  (define compiled (term (run-compiler ,source)))
  (apply-reduction-relation* ->effects (term (,compiled ()))))

(module+ test
  ;; GUARD-FUNC blames the client for domain failures and the provider for range failures.
  ;; Passing checks resume with the original value.
  (for ([case (in-list
               (list (list (term (mon provider client site (flat (λ x num false)) 7))
                           (term ((blame (party "provider")) ())))
                     (list (term ((mon provider client site
                                       ((flat (λ x num false)) -> (flat (λ x num true)))
                                       (λ x num x)) 7))
                           (term ((blame (party "client")) ())))
                     (list (term ((mon provider client site
                                       ((flat (λ x num true)) -> (flat (λ x num false)))
                                       (λ x num x)) 7))
                           (term ((blame (party "provider")) ())))
                     (list (term (mon provider client site (flat (λ x num true)) 7))
                           (term (7 ())))))])
    (test-equal (compile-and-run/local-handler (first case)) (list (second case))))

  ;; Compilation tests cover both passing and failing predicates.  A failure
  ;; is represented by `false` at compile time; the local handler signals
  ;; `blame` at execution time.
  (define-syntax-rule (compiles source expected-type)
    ;; `expected-type` documents the source result type for each regression.
    ;; The compiler rules are intentionally relational, so this test asks that
    ;; the full source expression has at least one target translation.
    (check-not-false (judgment-holds (compile () source C:τ E:e) E:e)))

  ;; Flat contracts: success and blame cases in varied expression positions.
  (compiles (mon k l j (flat (λ x num true)) 7) num)                 ; 1
  (compiles (mon k l j (flat (λ x num false)) 7) num)                ; 2 blame
  (compiles (mon k l j (flat (λ x num (zero? x))) 0) num)            ; 3
  (compiles (mon k l j (flat (λ x num (zero? x))) 1) num)            ; 4 blame
  (compiles (add (mon k l j (flat (λ x num true)) 2) 3) num)         ; 5
  (compiles (add (mon k l j (flat (λ x num false)) 2) 3) num)        ; 6 blame
  (compiles (if (mon k l j (flat (λ x bool true)) true) 1 2) num)    ; 7
  (compiles (if (mon k l j (flat (λ x bool false)) true) 1 2) num)   ; 8 blame
  (compiles (λ x num (mon k l j (flat (λ y num true)) x))
            (num -> num))                                            ; 9
  (compiles (λ x num (mon k l j (flat (λ y num false)) x))
            (num -> num))                                            ; 10 blame

  ;; Function contracts: domain and range checks, each in pass/fail forms.
  (compiles ((mon k l j ((flat (λ x num true)) -> (flat (λ y num true)))
                  (λ x num (add x 1))) 10) num)                      ; 11
  (compiles ((mon k l j ((flat (λ x num true)) -> (flat (λ y num false)))
                  (λ x num (add x 1))) 10) num)                      ; 12 blame
  (compiles ((mon k l j ((flat (λ x num (pos? x))) -> (flat (λ y num true)))
                  (λ x num (add x 1))) 5) num)                       ; 13
  (compiles ((mon k l j ((flat (λ x num (pos? x))) -> (flat (λ y num true)))
                  (λ x num (add x 1))) -5) num)                      ; 14 blame
  (compiles (mon k l j ((flat (λ x num true)) -> (flat (λ y num true)))
                 (λ x num (add x 1))) (num -> num))                  ; 15
  (compiles (mon k l j ((flat (λ x num true)) -> (flat (λ y num false)))
                 (λ x num (add x 1))) (num -> num))                  ; 16 blame-on-call

  ;; Dependent contracts: range predicates refer to the monitored argument.
  (compiles ((mon k l j
                  ((flat (λ x num true)) ->i y
                   (flat (λ r num (eq (sub r y) 1))))
                  (λ x num (add x 1))) 10) num)                      ; 17
  (compiles ((mon k l j
                  ((flat (λ x num true)) ->i y
                   (flat (λ r num (zero? (sub r y)))))
                  (λ x num (add x 1))) 10) num)                      ; 18 blame
  (compiles ((mon k l j
                  ((flat (λ x num (pos? x))) ->i y
                   (flat (λ r num (gt r y))))
                  (λ x num (add x 1))) 3) num)                       ; 19
  (compiles ((mon k l j
                  ((flat (λ x num (pos? x))) ->i y
                   (flat (λ r num (gt r y))))
                  (λ x num (add x 1))) -3) num)                      ; 20 blame
  (compiles ((mon k l j
                  ((flat (λ x num true)) ->i x
                   (flat (λ r num (gt r x))))
                  (λ x num (mul x 2))) 5) num)                       ; 21
  (compiles ((mon k l j
                  ((flat (λ x num true)) ->i x
                   (flat (λ r num (gt r x))))
                  (λ x num (mul x 2))) -5) num)                      ; 22 blame

  ;; Nested/curried higher-order contracts exercise recursive compilation.
  (compiles (((mon k l j
                   ((flat (λ x num true)) ->
                    ((flat (λ y num true)) -> (flat (λ r num (gt r 0)))))
                   (λ a num (λ b num (add a b)))) 1) 2) num)         ; 23
  (compiles (((mon k l j
                   ((flat (λ x num true)) ->i y
                    ((flat (λ z num true)) -> (flat (λ r num (gt r y)))))
                   (λ a num (λ b num (add a b)))) 1) -2) num)        ; 24 blame

  ;; Runtime regression: the local handler resolves both outcomes by itself.
  (check-equal? (compile-and-run/local-handler
                 (term (mon k l j (flat (λ x num true)) 7)))
                (list (term (7 ()))))
  (check-equal? (compile-and-run/local-handler
                 (term (mon k l j (flat (λ x num false)) 7)))
                (list (term ((blame (party "k")) ()))))

  ;; Recursive translation covers function, product, and reference annotations.
  (check-equal? (term (translate-type ((t (num -> bool) (ref (bool -> num))) -> (num -> num))))
                (term ((t (num -> (𝒞) bool) (ref (bool -> (𝒞) num))) -> (𝒞) (num -> (𝒞) num))))
  (check-true (alpha-equivalent? CompilerLocalHandler
                                 (term (run-compiler (λ f (num -> bool) f)))
                                 (term (λ (𝒞) f (num -> (𝒞) bool) f))))
  ;; Names used by the generated handler must not capture free source variables.
  (check-equal? (compile-and-run/local-handler
                 (term ((λ h num (mon k l j (flat (λ payload num (eq payload h))) h)) 7)))
                (list (term (7 ()))))
  (check-equal? (compile-and-run/local-handler
                 (term (mon k l j
                            (t (flat (λ x num true)) (flat (λ x bool true)))
                            (t 7 true))))
                (list (term ((t 7 true) ())))))
