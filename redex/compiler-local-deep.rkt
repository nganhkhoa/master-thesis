#lang racket

(provide CompilerLocalDeep compile run-compiler run-type
         compile-and-run/local-deep)

(require redex/reduction-semantics)

(require "contracts.rkt")
;; Every flat monitor installs a deep handler at its point of use.
(require "effects.rkt")

(define-union-language CompilerLocalDeep (C: Contracts) (E: Effects))

(define-metafunction CompilerLocalDeep
  extend : C:Γ C:x C:τ -> C:Γ
  [(extend ((C:x_1 C:τ_1) ...) C:x C:τ)
   ((C:x C:τ) (C:x_1 C:τ_1) ...)])

(define-metafunction CompilerLocalDeep
  lookup : C:Γ C:x -> C:τ
  [(lookup ((C:x_1 C:τ_1) ... (C:x C:τ) (C:x_2 C:τ_2) ...) C:x) C:τ])

;; Use the conservative 𝒞 row throughout: a shallow resumption retains 𝒞,
;; so both modalities need this outer row for identical, typable clauses.
;; Translate annotations recursively.
(define-metafunction CompilerLocalDeep
  translate-type : C:τ -> E:τ
  [(translate-type (C:τ_1 -> C:τ_2))
   ((translate-type C:τ_1) -> (𝒞) (translate-type C:τ_2))]
  [(translate-type (t C:τ_1 C:τ_2))
   (t (translate-type C:τ_1) (translate-type C:τ_2))]
  [(translate-type (ref C:τ)) (ref (translate-type C:τ))]
  [(translate-type num) num]
  [(translate-type bool) bool]
  [(translate-type unit) unit])

(define-metafunction CompilerLocalDeep
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

(define-judgment-form CompilerLocalDeep
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

  [(where C:Γ_new (extend C:Γ C:x C:τ))
   (compile C:Γ_new C:e C:τ E:e_body)
   (where E:x ,(term C:x))
   (where E:τ (translate-type C:τ))
   ------------------------------------------------------------------------ "C-Fix"
   (compile C:Γ (μ C:x C:τ C:e) C:τ (μ E:x E:τ E:e_body))]

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
            (d-handle (𝒞)
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

(define-metafunction CompilerLocalDeep
  run-compiler : C:e -> E:e
  [(run-compiler C:e_in) E:e_out
   (where (E:e_out E:e_extra ...) ,(judgment-holds (compile () C:e_in C:τ E:e) E:e))
   (side-condition (= 1 (length (term (E:e_out E:e_extra ...)))))])
(define-metafunction CompilerLocalDeep
  run-type : C:e -> C:τ
  [(run-type C:e_in) C:τ_out
   (where (C:τ_out C:τ_extra ...) ,(judgment-holds (compile () C:e_in C:τ E:e) C:τ))
   (side-condition (= 1 (length (term (C:τ_out C:τ_extra ...)))))])

;; No recursive or global wrapper is needed: each flat monitor has a frame.
(define (compile-and-run/local-deep source)
  (define compiled (term (run-compiler ,source)))
  (apply-reduction-relation* ->effects (term (,compiled ()))))

(module* trace-support #f
  (provide nested-pass nested-fail trace)
  (define nested-pass
    (term (((mon provider client site
                 ((flat (λ x num true)) ->i y
                  ((flat (λ z num true)) ->i w
                   (flat (λ r num (eq r (add y w))))))
                 (λ a num (λ b num (add a b)))) 2) 3)))
  (define nested-fail
    (term (((mon provider client site
                 ((flat (λ x num true)) ->i y
                  ((flat (λ z num true)) ->i w
                   (flat (λ r num (eq r (add y w))))))
                 (λ a num (λ b num (sub a b)))) 2) 3)))

  ;; Reproducible, non-GUI trace with rule names; fail on nondeterminism or a
  ;; runaway trace instead of silently choosing a branch. Invoke with --trace.
  (define (trace relation initial)
    (let loop ([state initial] [n 0] [rules '()])
      (when (> n 1000) (error 'trace "step limit exceeded"))
      (define next (apply-reduction-relation/tag-with-names relation state))
      (cond [(null? next) (values n (reverse rules) state)]
            [(null? (cdr next))
             (loop (cadar next) (add1 n) (cons (caar next) rules))]
            [else (error 'trace "nondeterministic state: ~s" state)])))
)

(module+ test
  (require rackunit "contracts.rkt"
           (submod ".." trace-support)
           (prefix-in shallow: "compiler-local.rkt"))

  ;; Source blame can remain inside an evaluation context; target blame aborts
  ;; to the top. Compare its positive party, not its different representation.
  (define (source-blame t)
    (match t
      [`(blame ,k ,_) k]
      [(? list?) (ormap source-blame t)]
      [_ #f]))
  (define (source-observation p)
    (match (apply-reduction-relation* ->contracts (term (,p ())))
      [(list (list e _)) (cond [(source-blame e) => (λ (k) `(blame ,k))]
                               [else e])]
      [other `(unexpected ,other)]))
  (define (target-observation p)
    (match (compile-and-run/local-deep p)
      [(list (list `(blame (party ,p)) _)) `(blame ,(string->symbol p))]
      [(list (list e _)) e]
      [other `(unexpected ,other)]))

  (define cases
    (list
     (list (term 7) 7)
     (list (term (mon provider client site (flat (λ x num true)) 7)) 7)
     (list (term (mon provider client site (flat (λ x num false)) 7)) '(blame provider))
     (list (term (add (mon p q s (flat (λ x num true)) 2)
                      (mon p q s (flat (λ x num true)) 3))) 5)
     (list (term (mon p q s (t (flat (λ x num true)) (flat (λ b bool true)))
                      (t 2 true))) '(t 2 true))
     (list (term ((mon provider client site
                       ((flat (λ x num true)) -> (flat (λ r num false)))
                       (λ x num x)) 3)) '(blame provider))
     ;; Dependent GUARD-DEP flips k/l for the function argument.
     (list (term ((mon provider client site
                       ((flat (λ x num false)) ->i y (flat (λ r num true)))
                       (λ x num x)) 3)) '(blame client))
     (list nested-pass 5)
     (list nested-fail '(blame provider))
     ;; A monitor inside the predicate requires a nested local handler.
     (list (term (mon outer peer site
                      (flat (λ x num (mon inner peer site (flat (λ b bool true)) true)))
                      9)) 9)
     (list (term (mon outer peer site
                      (flat (λ x num (mon inner peer site (flat (λ b bool false)) true)))
                      9)) '(blame inner))))
  (define Σ-check
    (term ((𝒞 : (𝒞 -> (∀ α ((t party (t (α -> (𝒞) bool) α)) -> () α)))))))
  (for ([case (in-list cases)])
    (match-define (list p expected) case)
    (check-equal? (source-observation p) expected (format "source ~s" p))
    (check-equal? (target-observation p) expected (format "target ~s" p))
    (define compiled (term (run-compiler ,p)))
    (define shallow-compiled (term (shallow:run-compiler ,p)))
    (check-equal? (match (shallow:compile-and-run/local-handler p)
                    [(list (list `(blame (party ,name)) _)) `(blame ,(string->symbol name))]
                    [(list (list e _)) e]
                    [other `(unexpected ,other)]) expected
                  (format "shallow target ~s" p))
    ;; Identical lowering, modulo frame modality, including nested checks.
    (define (erase-modality t)
      (cond [(eq? t 's-handle) 'd-handle]
            [(pair? t) (map erase-modality t)]
            [else t]))
    (check-true (alpha-equivalent? CompilerLocalDeep
                                   (erase-modality shallow-compiled) compiled)
                (format "same structure ~s" p)))
  ;; Non-dependent domains swap parties under GUARD-FUNC.
  (define domain-fail
    (term ((mon provider client site
                ((flat (λ x num false)) -> (flat (λ r num true)))
                (λ x num x)) 3)))
  (check-equal? (source-observation domain-fail) '(blame client))
  (check-equal? (target-observation domain-fail) '(blame client))
  ;; Direct deep lowering uses a frame, not a handler value or recursive wrapper.
  (define generated (term (run-compiler (mon p q s (flat (λ x num true)) 7))))
  (define (contains-symbol? s t)
    (or (eq? s t) (and (pair? t) (ormap (λ (x) (contains-symbol? s x)) t))))
  (check-true (contains-symbol? 'd-handle generated))
  (check-false (contains-symbol? 's-handle generated))
  (check-false (contains-symbol? 'μ generated))
  (define shallow-generated
    (term (shallow:run-compiler (mon p q s (flat (λ x num true)) 7))))
  (check-true (contains-symbol? 's-handle shallow-generated))
  (check-false (contains-symbol? 'd-handle shallow-generated))
  (check-false (contains-symbol? 'μ shallow-generated))
  ;; Assert the literal proof shape, including an unevaluated nested payload.
  (define nested-payload-source
    (term (mon outer peer site (flat (λ x num true))
               (mon inner peer site (flat (λ x num true)) 7))))
  (for ([compiled (in-list (list (term (shallow:run-compiler ,nested-payload-source))
                                 (term (run-compiler ,nested-payload-source))))]
        [mode (in-list '(s-handle d-handle))])
    (match compiled
      [`(,actual-mode (𝒞) ,_ ((perform () 𝒞 num)
                               (t (party "outer") (t ,predicate ,inner))))
       (check-equal? actual-mode mode)
       (check-true (match predicate [`(λ (𝒞) ,_ num true) #t] [_ #f]))
       (check-true (match inner
                     [`(,inner-mode (𝒞) ,_ ((perform () 𝒞 num)
                                             (t (party "inner") (t ,_ 7))))
                      (eq? inner-mode mode)]
                     [_ #f]))]
      [_ (fail-check (format "expected direct handler around original payload: ~s" compiled))]))
  ;; The conservative row is necessary under the current handler rules.
  (check-equal? (judgment-holds (⊢ ,Σ-check () ,shallow-generated τ ()) τ) '())
  (check-equal? (judgment-holds (⊢ ,Σ-check () ,generated τ ()) τ) '()))

(module+ main
  (require (submod ".." trace-support))
  (unless (equal? (vector->list (current-command-line-arguments)) '("--trace"))
    (error 'main "use --trace"))
  (for ([p (list nested-pass nested-fail)] [label '(pass fail)])
    (printf "~a\n" label)
    (for ([kind '(source target)])
      (define initial
        (if (eq? kind 'source) (term (,p ()))
            (term (,(term (run-compiler ,p)) ()))))
      (define-values (n rules last)
        (trace (if (eq? kind 'source) ->contracts ->effects) initial))
      (printf "  ~a: ~a steps; rules ~s\n  final: ~s\n" kind n rules last))))
