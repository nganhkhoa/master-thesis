#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(require "base.rkt")

(define-extended-language Effects Base
  (K ::= * (K -> K) eff lab)
  (modality ::= deep shallow)

  (ε ::= (effect ...))

  (τ ::= ....
         party
         α
         (τ -> ε τ)
         (∀ α τ))

  ;; Recursive annotations have an explicit eliminable outer constructor.
  (T ::= (τ -> ε τ) (∀ α τ))

  (h ::= ((op f) ...))

  ;; The two clause rows are compared extensionally by the typing rule;
  ;; requiring the same syntax here rejects equivalent reordered rows.
  (f ::= (Λ α (λ ε_1 x_1 τ_1 (λ ε_2 k τ_2 e))))

  ;; Recursion is provided only by the value grammar below.
  (e ::= v (t e e) (e e) (injl e) (injr e) (o e ...)
         (if e e e) (new e) (get e) (set e e)
         ;; surface
         (λ ε x τ e) ;; added epsilon here
         (e τ)
         ;; dynamic handler frames, retaining the handler's modality
         (d-handle ε h e)
         (s-handle ε h e)
         ;; dynamic
         (blame e))

  (v ::= ....
         (μ x T v)
         (party p)
         (λ ε x τ e)
         (Λ α v)
         ;; d-handler reinstalls itself around a resumed continuation;
         ;; s-handler resumes its continuation without reinstalling itself.
         (d-handler ε h)
         (s-handler ε h)
         (perform ε op τ))

  (E ::= ....
         (E τ)
         (d-handle ε h E)
         (s-handle ε h E)
         (blame E))

  (Σ ::= ((effect : (op -> τ) ...) ...))

  (α  ::= variable-not-otherwise-mentioned)
  (op ::= variable-not-otherwise-mentioned)
  ;; Strings are atomic labels: substitution never changes a party name.
  (p ::= string)

  ;; effect name
  (effect ::= variable-not-otherwise-mentioned)

  ;; to make continuation easy to write
  (k  ::= variable-not-otherwise-mentioned)

  #:binding-forms
  (∀ α τ #:refers-to α)
  (Λ α v #:refers-to α)
  (μ x T v #:refers-to x)
  (λ ε x τ e #:refers-to x))

(define-metafunction Effects
  in-handler : op h -> boolean
  [(in-handler op ((op_1 f_1) ... (op f) (op_2 f_2) ... )) #true]
  [(in-handler _ _) #false])

(define-metafunction Effects
  find-op-in-handler : op h -> (τ α f)
  [(find-op-in-handler
     op
     ((op_1 f_1) ... (op (Λ α (λ ε_1 x τ_1 (λ ε_2 k τ_2 e)))) (op_2 f_2) ...))
   (τ_2 α (Λ α (λ ε_1 x τ_1 (λ ε_2 k τ_2 e))))])

(define-metafunction Effects
  append-ops : (op ...) (op ...) -> (op ...)
  [(append-ops (op_1 ...) (op_2 ...))
   (op_1 ... op_2 ...)])

(define-metafunction Effects
  bop : E -> (op ...)
  [(bop hole) ()]
  [(bop (E e)) (bop E)]
  [(bop (v E)) (bop E)]
  [(bop (t E e)) (bop E)]
  [(bop (t v E)) (bop E)]
  [(bop (injl E)) (bop E)]
  [(bop (injr E)) (bop E)]
  [(bop (o v ... E e ...)) (bop E)]
  [(bop (new E)) (bop E)]
  [(bop (get E)) (bop E)]
  [(bop (set E e)) (bop E)]
  [(bop (set v E)) (bop E)]
  [(bop (blame E)) (bop E)]
  [(bop (if E e_1 e_2)) (bop E)]

  ;; not sure about this lol
  [(bop (E τ)) (bop E)]

  [(bop (d-handle ε ((op f) ...) E))
   (append-ops (op ...) (bop E))]
  [(bop (s-handle ε ((op f) ...) E))
   (append-ops (op ...) (bop E))])

(define-metafunction Effects
  not-in : op (op ...) -> boolean
  [(not-in op (op_1 ... op op_2 ...)) #false]
  [(not-in op _) #true])

(define-metafunction Effects
  unhandled : op E -> boolean
  [(unhandled op E) (not-in op (bop E))])

(define-metafunction Effects
  extend : Γ x τ -> Γ
  [(extend ((x_1 τ_1) ...) x τ)
   ((x τ) (x_1 τ_1) ...)])

(define-metafunction Effects
  find-effect : Σ op -> (effect τ)
  [(find-effect ((effect_1 : (op_1 -> τ_1) ...) ...
                 (effect : (op_2 -> τ_2) ... (op -> τ) (op_3 -> τ_3) ...)
                 (effect_2 : (op_4 -> τ_4) ...) ...)
                op)
   (effect τ)])

(define-metafunction Effects
  lookup : Γ x -> τ
  [(lookup ((x_1 τ_1) ... (x τ) (x_2 τ_2) ...) x) τ])


(define-metafunction Effects
  lookup-op : Σ op -> (effect τ)
  ;; Scans the environment, finds the op, and returns its label and type signature
  [(lookup-op (_ ... (effect : _ ... (op -> τ_sig) _ ...) _ ...) op)
   (effect τ_sig)])

(define-metafunction Effects
  same-effects? : ε ε -> boolean
  [(same-effects? (effect_1 ...) (effect_2 ...))
   ,(equal? (sort (remove-duplicates (term (effect_1 ...))) symbol<?)
            (sort (remove-duplicates (term (effect_2 ...))) symbol<?))])

;; An expression may run in an ambient row containing additional effects.
(define-metafunction Effects
  effects-subset? : ε ε -> boolean
  [(effects-subset? (effect_1 ...) (effect_2 ...))
   ,(andmap (lambda (label) (if (member label (term (effect_2 ...))) #t #f))
            (term (effect_1 ...)))])

(define-metafunction Effects
  types-equiv? : τ τ -> boolean

  ;; Base types
  [(types-equiv? num num) #true]
  [(types-equiv? bool bool) #true]
  [(types-equiv? unit unit) #true]
  [(types-equiv? party party) #true]
  [(types-equiv? (ref τ_1) (ref τ_2)) (types-equiv? τ_1 τ_2)]
  [(types-equiv? α α) #true]

  ;; Arrow types (The important one!)
  [(types-equiv? (τ_1 -> ε_1 τ_2) (τ_3 -> ε_2 τ_4))
   ,(and (term (types-equiv? τ_1 τ_3))
         (term (types-equiv? τ_2 τ_4))
         (term (same-effects? ε_1 ε_2)))]

  ;; Compound types
  [(types-equiv? (t τ_1 τ_2) (t τ_3 τ_4))
   ,(and (term (types-equiv? τ_1 τ_3))
         (term (types-equiv? τ_2 τ_4)))]
  [(types-equiv? (∀ α_1 τ_1) (∀ α_2 τ_2))
   (types-equiv? (substitute τ_1 α_1 α_fresh)
                 (substitute τ_2 α_2 α_fresh))
   (where α_fresh ,(variable-not-in (term (α_1 α_2 τ_1 τ_2)) 'fresh))]

  ;; Fallback
  [(types-equiv? _ _) #false])

;; Deep resumptions use the outer row; shallow resumptions retain the handled effect.
;; Effect rows contain concrete labels, so freshness only needs to inspect types.
(define (free-type-vars t)
  (match t
    [`(∀ ,a ,body) (remove a (free-type-vars body))]
    [`(,a -> ,_ ,b) (append (free-type-vars a) (free-type-vars b))]
    [`(,a -> ,b) (append (free-type-vars a) (free-type-vars b))]
    [`(t ,a ,b) (append (free-type-vars a) (free-type-vars b))]
    [`(ref ,a) (free-type-vars a)]
    [(? symbol? a) (if (member a '(num bool unit party)) '() (list a))]
    [_ '()]))
(define-judgment-form Effects
  #:mode (⊢_ops/mod I I I I O O O)
  #:contract (⊢_ops/mod modality Σ Γ ((op f) ...) τ effect ε)

  [(where ((effect_list (∀ α (τ_arg -> () τ_res))) ...) ((lookup-op Σ op) ...))
   (⊢_val Σ Γ f τ_f) ...
   (where ((∀ α_f (τ_arg-f -> ε_first
                     ((τ_res-f -> ε_k τ_k) -> ε_clause τ_out-f))) ...) (τ_f ...))
   (where (effect_out effect_rest ...) (effect_list ...))
   (where (τ_out τ_rest ...) (τ_out-f ...))
   (where (ε_out ε_rest ...) (ε_clause ...))
   (side-condition
    ,(andmap values
       (term ((types-equiv? (substitute τ_arg α α_f) τ_arg-f) ...))))
   (side-condition
    ,(andmap values
       (term ((types-equiv? (substitute τ_res α α_f) τ_res-f) ...))))
   ;; Every operation of the handled effect must have exactly one clause.
   (side-condition
    ,(let* ([entry (assoc (term effect_out) (term Σ))]
            [declared (map first (cddr entry))]
            [actual (term (op ...))])
       (and (= (length actual) (length (remove-duplicates actual)))
            (equal? (sort declared symbol<?) (sort actual symbol<?)))))
   (side-condition ,(andmap values (term ((types-equiv? τ_k τ_out) ...))))
   (side-condition ,(andmap values (term ((types-equiv? τ_rest τ_out) ...))))
   (side-condition ,(andmap (lambda (x) (equal? x (term effect_out)))
                            (term (effect_rest ...))))
   (side-condition ,(andmap values (term ((same-effects? ε_rest ε_out) ...))))
   (side-condition ,(andmap values (term ((same-effects? ε_first ε_out) ...))))
   (side-condition
    ,(andmap (lambda (a) (not (member a (free-type-vars (term τ_out)))))
             (term (α_f ...))))
   (where ε_resume (resume-effects modality effect_out ε_out))
   (side-condition ,(andmap values (term ((same-effects? ε_k ε_resume) ...))))
   --------------------------------------------------------- "T-E-Ops"
   (⊢_ops/mod modality Σ Γ ((op f) ...) τ_out effect_out ε_out)])

(define-metafunction Effects
  resume-effects : modality effect ε -> ε
  [(resume-effects deep effect ε) ε]
  [(resume-effects shallow effect (effect_1 ...)) (effect effect_1 ...)])

;; Preserve the original public judgment as the deep-handler variant.
(define-judgment-form Effects
  #:mode (⊢_ops I I I O O O)
  #:contract (⊢_ops Σ Γ ((op f) ...) τ effect ε)
  [(⊢_ops/mod deep Σ Γ h τ effect ε)
   ----------------------------------
   (⊢_ops Σ Γ h τ effect ε)])

(define-judgment-form Effects
  #:mode (⊢_val I I I O)
  #:contract (⊢_val Σ Γ v τ)

  [(where τ (lookup Γ x))
   ---------------------- "T-E-Var"
   (⊢_val Σ Γ x τ)]


  [------------------ "T-E-Num"
   (⊢_val Σ Γ n num)]

  [------------------- "T-E-Bool"
   (⊢_val Σ Γ b bool)]

  [---------------------- "T-E-Party"
   (⊢_val Σ Γ (party p) party)]

  [---------------------- "T-E-Unit"
   (⊢_val Σ Γ unit unit)]

  [(⊢_val Σ Γ v_1 τ_1)
   (⊢_val Σ Γ v_2 τ_2)
   ------------------------------------ "T-E-Tuple"
   (⊢_val Σ Γ (t v_1 v_2) (t τ_1 τ_2))]

  [(where Γ_0 (extend Γ x T))
   (⊢_val Σ Γ_0 v τ_body)
   (side-condition ,(term (types-equiv? T τ_body)))
   ------------------------------------ "T-E-Rec"
   (⊢_val Σ Γ (μ x T v) T)]

  [(where Γ_0 (extend Γ x τ_1))
   (⊢ Σ Γ_0 e τ_2 ())
   ---------------------------------------- "T-E-Abs-pure"
   (⊢_val Σ Γ (λ x τ_1 e) (τ_1 -> () τ_2))]

  [(where Γ_0 (extend Γ x τ_1))
   (⊢ Σ Γ_0 e τ_2 ε)
   ----------------------------------------- "T-E-Abs"
   (⊢_val Σ Γ (λ ε x τ_1 e) (τ_1 -> ε τ_2))]

  [(⊢_val Σ Γ v τ)
   ---------------------------- "T-E-Tabs"
   (⊢_val Σ Γ (Λ α v) (∀ α τ))]

  [
   (where (effect_1 τ_1) (find-effect Σ op))
   (where (∀ α (τ_2 -> () τ_3)) τ_1)
   ------------------------------------------------------ "T-E-Perform"
   (⊢_val Σ Γ (perform (effect ...) op τ)
        ((substitute τ_2 α τ)
         -> (effect_1 effect ...) (substitute τ_3 α τ)))]

  [(⊢_ops/mod deep Σ Γ h τ effect_0 ε_ops)
   (where (effect_1 ...) ε_ops)
   (side-condition (term (same-effects? ε ε_ops)))
   ------------------------------------------- "T-E-D-Handler"
   (⊢_val Σ Γ (d-handler ε h)
          ((unit -> (effect_0 effect_1 ...) τ)
           -> ε τ))]

  [(⊢_ops/mod shallow Σ Γ h τ effect_0 ε_ops)
   (where (effect_1 ...) ε_ops)
   (side-condition (term (same-effects? ε ε_ops)))
   ------------------------------------------- "T-E-S-Handler"
   (⊢_val Σ Γ (s-handler ε h)
          ((unit -> (effect_0 effect_1 ...) τ)
           -> ε τ))]

)

(define-judgment-form Effects
  #:mode (⊢ I I I O I)
  #:contract (⊢ Σ Γ e τ ε)

  [(⊢_val Σ Γ v τ)
   -------------- "T-E-Val"
   (⊢ Σ Γ v τ ε)]

  [(⊢ Σ Γ e_1 (τ_1 -> ε_0 τ_2) ε)
   (⊢_check Σ Γ e_2 τ_1 ε)
   (side-condition ,(term (effects-subset? ε_0 ε)))
   ---------------------------- "T-E-App"
   (⊢ Σ Γ (e_1 e_2) τ_2 ε)]

  [(⊢ Σ Γ e (∀ α τ_1) ε)
   ------------------------------------ "T-TApp"
   (⊢ Σ Γ (e τ) (substitute τ_1 α τ) ε)]

  [(⊢ Σ Γ e (t τ_1 τ_2) ε)
   ----------------------------- "T-Proj-L"
   (⊢ Σ Γ (injl e) τ_1 ε)]

  [(⊢ Σ Γ e (t τ_1 τ_2) ε)
   ----------------------------- "T-Proj-R"
   (⊢ Σ Γ (injr e) τ_2 ε)]

  ;; Either branch can provide the type; a blame expression cannot synthesize one.
  [(⊢_check Σ Γ e_1 bool ε)
   (⊢ Σ Γ e_2 τ ε)
   (⊢_check Σ Γ e_3 τ ε)
   ----------------------------- "T-If-Then"
   (⊢ Σ Γ (if e_1 e_2 e_3) τ ε)]

  [(⊢_check Σ Γ e_1 bool ε)
   (⊢ Σ Γ e_3 τ ε)
   (⊢_check Σ Γ e_2 τ ε)
   ----------------------------- "T-If-Else"
   (⊢ Σ Γ (if e_1 e_2 e_3) τ ε)]

  ;; N-ary Operator Rule
  [(where ((τ_arg ...) τ_out) (op-type o))
   (⊢_check Σ Γ e τ_arg ε) ...
   -------------------------------------- "T-Op"
   (⊢ Σ Γ (o e ...) τ_out ε)]

  ;; Stateful Typing Rules
  [(⊢ Σ Γ e τ ε)
   ------------------------- "T-New"
   (⊢ Σ Γ (new e) (ref τ) ε)]

  [(⊢ Σ Γ e (ref τ) ε)
   ------------------------- "T-Get"
   (⊢ Σ Γ (get e) τ ε)]

  [(⊢ Σ Γ e_1 (ref τ) ε)
   (⊢_check Σ Γ e_2 τ ε)
   ------------------------- "T-Set"
   (⊢ Σ Γ (set e_1 e_2) unit ε)]

  [(⊢ Σ Γ e_1 τ_1 ε)
   (⊢ Σ Γ e_2 τ_2 ε)
   ---------------------------------- "T-E-Tuple"
   (⊢ Σ Γ (t e_1 e_2) (t τ_1 τ_2) ε)]

  [(⊢_ops/mod deep Σ Γ h τ effect ε_out)
   (side-condition (term (same-effects? ε ε_out)))
   (where ε_body (resume-effects shallow effect ε_out))
   (⊢_check Σ Γ e τ ε_body)
   ----------------------------------- "T-D-Handle"
   (⊢ Σ Γ (d-handle ε h e) τ ε)]

  [(⊢_ops/mod shallow Σ Γ h τ effect ε_out)
   (side-condition (term (same-effects? ε ε_out)))
   (where ε_body (resume-effects shallow effect ε_out))
   (⊢_check Σ Γ e τ ε_body)
   ----------------------------------- "T-S-Handle"
   (⊢ Σ Γ (s-handle ε h e) τ ε)]
)

;; Checking has an input result type, so blame does not need to enumerate
;; arbitrary types. Checking conditionals directly also handles two blame arms.
(define-judgment-form Effects
  #:mode (⊢_check I I I I I)
  #:contract (⊢_check Σ Γ e τ ε)

  [(⊢_check Σ Γ e party ε)
   ------------------------------ "T-Check-Blame"
   (⊢_check Σ Γ (blame e) τ ε)]

  [(⊢_check Σ Γ e_1 bool ε)
   (⊢_check Σ Γ e_2 τ ε)
   (⊢_check Σ Γ e_3 τ ε)
   ------------------------------ "T-Check-If"
   (⊢_check Σ Γ (if e_1 e_2 e_3) τ ε)]

  [(⊢ Σ Γ e τ_actual ε)
   (side-condition ,(term (types-equiv? τ τ_actual)))
   ------------------------------ "T-Check-Synth"
   (⊢_check Σ Γ e τ ε)])

;; during evaluation we can ignore types and effects
;; just inherit reduction rules from base
(define ->effects
  (extend-reduction-relation ->base Effects
    ;; Recursive values unfold only when eliminated.
    [==> ((μ x (τ_1 -> ε τ_2) v_body) v_arg)
         ((substitute v_body x (μ x (τ_1 -> ε τ_2) v_body)) v_arg)
         Fix]

    [==> ((μ x (∀ α τ_body) v_body) τ_arg)
         ((substitute v_body x (μ x (∀ α τ_body) v_body)) τ_arg)
         REC-TAPP]

    [==> ((λ ε x τ e) v)
         (substitute e x v)
         APP-EFFECT]

    [==> ((Λ α v) τ)
         (substitute v α τ)
         TAPP]

    [==> ((d-handler ε h) v)
         (d-handle ε h (v unit))
         D-HANDLER-VALUE]

    [==> ((s-handler ε h) v)
         (s-handle ε h (v unit))
         S-HANDLER-VALUE]

    [==> (d-handle ε h v)
         v
         D-HANDLE-VALUE]

    [==> (s-handle ε h v)
         v
         S-HANDLE-VALUE]

    [==> (d-handle ε h (in-hole E ((perform ε_1 op τ) v)))
         (((f τ) v) e)

         (side-condition (term (unhandled op E)))
         (side-condition (term (in-handler op h)))
         (where ((τ_arg -> ε_k τ_answer) α f) (find-op-in-handler op h))
         ;; The deep continuation runs the reinstated handler in the outer row.
         (where x_fresh ,(variable-not-in (term (E h τ)) 'resume))
         (where e (λ ε x_fresh (substitute τ_arg α τ)
                       (d-handle ε h (in-hole E x_fresh))))
         D-HANDLE-OP]

    [==> (s-handle ε h (in-hole E ((perform ε_1 op τ) v)))
         (((f τ) v) e)

         (side-condition (term (unhandled op E)))
         (side-condition (term (in-handler op h)))
         (where ((τ_arg -> ε_k τ_answer) α f) (find-op-in-handler op h))
         ;; A shallow handler is consumed by its operation: no reinstallation.
         (where x_fresh ,(variable-not-in (term (E h τ)) 'resume))
         (where e (λ ε_k x_fresh (substitute τ_arg α τ) (in-hole E x_fresh)))
         S-HANDLE-OP]

    ;; A completed blame aborts all surrounding frames, including handlers.
    ;; Excluding hole makes the terminal blame configuration irreducible.
    [--> ((in-hole E (blame (party p))) σ) ((blame (party p)) σ)
     (side-condition (not (equal? (term E) (term hole))))
     BLAME-PROPAGATE]

    with
    [(--> ((in-hole E before) σ) ((in-hole E after) σ))
     (==> before after)]))

(define-term Γ_init ())
(define-term mteff ())

(module+ test
  (require rackunit)

  ;; Recursion is a value, restricted to arrow/forall annotations and bodies
  ;; that are values; it unfolds only in the corresponding elimination form.
  (define-term rec-id (μ f (num -> () num) (λ () x num x)))
  (define-term rec-poly (μ f (∀ α (α -> () α)) (Λ α (λ () x α x))))
  (check-true (redex-match? Effects v (term rec-id)))
  (check-false (redex-match? Effects e (term (μ x num x))))
  (check-false (redex-match? Effects e (term (μ f (num -> () num) (blame (party "p"))))))
  (check-true (judgment-holds (⊢_val () () rec-id (num -> () num))))
  (check-true (judgment-holds (⊢_val () () rec-poly (∀ α (α -> () α)))))
  (check-false (judgment-holds (⊢_val () ()
    (μ f (num -> () num) (λ () x num true)) (num -> () num))))
  (check-equal? (apply-reduction-relation ->effects (term (rec-id ()))) '())
  (test-->> ->effects (term ((rec-id 7) ())) (term (7 ())))
  (test-->> ->effects (term (((rec-poly num) 7) ())) (term (7 ())))
  ;; Self-reference is substituted capture-avoidantly, and recursion can
  ;; itself be the body of a recursive value (including a diverging one).
  (check-true (judgment-holds (⊢_val () ()
    (μ f (num -> () num) f) (num -> () num))))
  (define looping-rec (term (((μ f (num -> () num) f) 1) ())))
  (define looping-steps (apply-reduction-relation ->effects looping-rec))
  (check-equal? (length looping-steps) 1)
  (check-true (alpha-equivalent? Effects (first looping-steps) looping-rec))
  (test-->> ->effects
    (term (((μ f (num -> () num)
               (λ () x num (if (zero? x) 0 (f (sub x 1))))) 2) ()))
    (term (0 ())))
  ;; The recursive binder scopes over the body, not its annotation.  Test
  ;; substitution through it with a colliding free variable and type name.
  (define rec-capture-step
    (first (apply-reduction-relation ->effects
      (term (((λ () x (num -> () num)
                 (μ y (num -> () num) (λ () z num x))) y) ())))))
  (check-true (alpha-equivalent? Effects rec-capture-step
    (term ((μ fresh (num -> () num) (λ () z num y)) ()))))
  (define rec-type-step
    (first (apply-reduction-relation ->effects
      (term (((Λ α (μ x (α -> () α) (λ () z α x))) num) ())))))
  (check-true (alpha-equivalent? Effects rec-type-step
    (term ((μ x (num -> () num) (λ () z num x)) ()))))
  ;; A recursive value with a free variable under a same-named lambda must
  ;; remain free after self-unfolding.
  (define unfold-capture-step
    (first (apply-reduction-relation ->effects
      (term (((μ f (num -> () num)
                  (λ () y num (if true w ((λ () w num (f y)) 0)))) 1) ())))))
  (check-true (alpha-equivalent? Effects unfold-capture-step
    (term (((λ () y num
               (if true w ((λ () fresh num
                              ((μ f (num -> () num)
                                  (λ () y num (if true w ((λ () w num (f y)) 0)))) y)) 0)))
            1) ()))))
  ;; A recursive value in an argument is passed without first unfolding it.
  (test-->> ->effects
            (term (((λ () f (num -> () num) 9) rec-id) ()))
            (term (9 ())))

  (define-term Σ-check
    ((con : (check -> (∀ α ((t party (t (α -> (con) bool) α)) -> () α))))))
  (define-term check-deep
    ((check (Λ β (λ (con) x (t party (t (β -> (con) bool) β))
                      (λ (con) k (β -> (con) num) (k (injr (injr x)))))))))
  (define-term check-bad-arg
    ((check (Λ β (λ (con) x num
                      (λ (con) k (β -> (con) num) (k 1)))))))
  (define-term check-bad-result
    ((check (Λ β (λ (con) x (t party (t (β -> (con) bool) β))
                      (λ (con) k (bool -> (con) num) (k true)))))))
  ;; Substitution through a handler clause must respect all three binders,
  ;; while preserving the restricted f grammar.
  (define handler-capture-step
    (first (apply-reduction-relation ->effects
      (term (((λ () x num
                 (d-handler () ((check (Λ α (λ () y num (λ () k num x)))))))
              y) ())))))
  (check-true (redex-match? Effects v (first handler-capture-step)))
  (check-true (alpha-equivalent? Effects handler-capture-step
    (term ((d-handler () ((check (Λ α (λ () fresh num (λ () k num y)))))) ()))))
  ;; Equivalent but syntactically different clause effect rows are allowed.
  (define-term check-reordered
    ((check (Λ β (λ (con other) x (t party (t (β -> (con) bool) β))
                      (λ (other con) k (β -> (con other) num) (k (injr (injr x)))))))))
  (check-true (redex-match? Effects h (term check-reordered)))
  (check-true (judgment-holds (⊢_ops/mod deep Σ-check () check-reordered num con (other con))))
  (check-true (judgment-holds (⊢_ops/mod deep Σ-check () check-deep num con (con))))
  (check-false (judgment-holds (⊢_ops/mod deep Σ-check () check-bad-arg num con (con))))
  (check-false (judgment-holds (⊢_ops/mod deep Σ-check () check-bad-result num con (con))))
  (check-true (judgment-holds (⊢_val Σ-check () (perform () check num)
    ((t party (t (num -> (con) bool) num)) -> (con) num))))
  (check-true (term (same-effects? (con con) (con))))

  ;; Deep resumes eliminate the handled effect; shallow resumes retain it.
  (define-term Σ-ping ((ping-eff : (ping -> (∀ α (num -> () num))))))
  (define-term ping-deep
    ((ping (Λ α (λ () x num (λ () k (num -> () num) (k x)))))))
  (define-term ping-shallow
    ((ping (Λ α (λ () x num (λ () k (num -> (ping-eff) num) 0))))))
  (check-true (judgment-holds (⊢_ops/mod deep Σ-ping () ping-deep num ping-eff ())))
  (check-false (judgment-holds (⊢_ops/mod shallow Σ-ping () ping-deep num ping-eff ())))
  (check-true (judgment-holds (⊢_ops/mod shallow Σ-ping () ping-shallow num ping-eff ())))
  (check-false (judgment-holds (⊢_ops/mod deep Σ-ping () ping-shallow num ping-eff ())))
  (check-true (judgment-holds (⊢_check Σ-ping ()
     (d-handle () ping-deep ((perform () ping num) 1)) num ())))
  (check-false (judgment-holds (⊢_check Σ-ping ()
     (d-handle () ping-shallow ((perform () ping num) 1)) num ())))

  ;; The operation rule instantiates the clause's bound type variable in the
  ;; captured continuation. The continuation binder must also avoid capture.
  (define-term Σ-poly ((poly-eff : (poly -> (∀ α (α -> () α))))))
  (define-term poly-deep
    ((poly (Λ α (λ () x α (λ () k (α -> () num) 7))))))
  (define-term poly-shallow
    ((poly (Λ α (λ () x α (λ () k (α -> (poly-eff) num) 7))))))
  (for ([mode '(deep shallow)] [handle '(d-handle s-handle)]
        [clause (list (term poly-deep) (term poly-shallow))])
    (check-true (judgment-holds (⊢_ops/mod ,mode Σ-poly () ,clause num poly-eff ())))
    (define start (term (,handle () ,clause
                                  (add resume ((perform () poly num) 1)))))
    (define steps (apply-reduction-relation ->effects (term (,start ()))))
    (check-equal? (length steps) 1)
    (match-define (list (list reduct _)) steps)
    (match-define `(,_ (λ ,row ,binder num ,_)) reduct)
    (check-not-equal? binder 'resume)
    (check-equal? row (if (eq? mode 'deep) '() '(poly-eff))))

  ;; Deep operation reduction preserves typing with its outer-row continuation.
  (define deep-start (term (d-handle () poly-deep ((perform () poly num) 1))))
  (check-true (judgment-holds (⊢_check Σ-poly () ,deep-start num ())))
  (define deep-next (first (apply-reduction-relation ->effects (term (,deep-start ())))))
  (check-true (judgment-holds (⊢_check Σ-poly () ,(first deep-next) num ())))

  ;; Labels are data, not variables; labels can also be computed at run time.
  (test-equal (judgment-holds (⊢ () () (party "client") τ ()) τ) (term (party)))
  (check-true (judgment-holds (⊢_check () () (blame (party "client")) num ())))
  (check-true (judgment-holds (⊢_check () () (blame (party "client")) bool ())))
  (check-false (judgment-holds (⊢_check () () (blame 1) num ())))
  (check-false (judgment-holds (⊢_check () () (party "client") num ())))
  (check-true (judgment-holds (⊢_check () ()
                             (if true (blame (party "a")) (blame (party "b"))) num ())))
  (test-equal (judgment-holds (⊢ () () (if true (blame (party "a")) 3) τ ()) τ)
              (term (num)))
  (test-equal (judgment-holds (⊢ () () (if true 3 (blame (party "a"))) τ ()) τ)
              (term (num)))
  (check-true (judgment-holds (⊢_check () () (add (blame (party "a")) 1) num ())))
  (check-true (judgment-holds (⊢_check () ()
                             ((λ () x num x) (blame (party "a"))) num ())))
  (test-->> ->effects
            (term ((add 1 (blame (injl (t (party "client") 42)))) ()))
            (term ((blame (party "client")) ())))
  (test-->> ->effects
            (term (((λ () label party (blame label)) (party "client")) ()))
            (term ((blame (party "client")) ())))
  (test-->> ->effects
            (term ((blame (blame (party "inner"))) ()))
            (term ((blame (party "inner")) ())))
  (test-->> ->effects
            (term ((d-handle () () (if true (blame (party "client")) 1)) ((cell 9))))
            (term ((blame (party "client")) ((cell 9)))))
  (check-equal? (apply-reduction-relation ->effects (term ((blame (party "client")) ()))) '())
  ;; Party names are constants, even when a binder has the same spelling.
  (test-->> ->effects
            (term (((λ client num (blame (party "client"))) 7) ()))
            (term ((blame (party "client")) ())))
  (check-true (judgment-holds (⊢_check () () (blame (party "client"))
                                       (num -> () bool) (con))))
  (define-term h-dup ((dup (Λ α (λ () x α (λ () k (α -> () num) (k (add x x)))))) ))
  (define-term h-get ((get (Λ α (λ () x α (λ () k α (λ () s num ((k s) s))))))))
  (define-term h-set ((set (Λ α (λ () x α (λ () k α (λ () s num ((k x) s))))))))

  (define-term h-dummy ((dummy (Λ α (λ () x α (λ () k (α -> () num) (k x)))))))

  (test-match Effects
    ((op f) ...)
    (term ((dup (Λ α (λ () x α (λ () k α (k x))))))))

  (test-match Effects
    h (term h-dup))

  (test-match Effects
    (d-handle ε h E)
    (term (d-handle (dup) h-dup (add hole 1))))

  (test-match Effects
    (d-handle ε h (in-hole (add hole 1) ((perform op τ) v)))
    (term (d-handle (dup) h-dup (add ((perform op τ) v) 1))))

  ;; (test-equal (first (judgment-holds (⊢ () () 1 τ ()) τ))
  ;;             (term num))

  ;; (test-equal (first (judgment-holds (⊢ () () (λ () x num 1) τ ()) τ))
  ;;             (term (num -> () num)))

  ;; (test-equal (first (judgment-holds (⊢ () () ((Λ α (λ () x α 1)) num) τ ()) τ))
  ;;             (term (num -> () num)))


  (test-match Effects Σ (term ((some-eff : (getval -> (∀ α (α -> () num)))))))
  (test-match Effects Γ (term Γ_init))
  (test-match Effects h (term ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10))))))))

  (judgment-holds
    (⊢_val ()
         Γ_init
         (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10))))
         τ)
    τ)

  ;; (judgment-holds
  ;;   (⊢_ops ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;          Γ_init
  ;;          ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10))))))
  ;;          τ effect ε)
  ;;   (τ effect ε))

  ;; (judgment-holds
  ;;   (⊢_val ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;          Γ_init
  ;;          (perform () getval unit)
  ;;          τ)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢_val ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;          Γ_init
  ;;          (d-handler () ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num)
  ;;                                                             (k 10)))))))
  ;;          τ)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;      Γ_init
  ;;      ((d-handler () ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10)))))))
  ;;       (perform () getval unit))
  ;;      τ
  ;;      mteff)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;      Γ_init
  ;;      ((d-handler () ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10)))))))
  ;;       (λ (some-eff) y unit ((perform () getval unit) unit)))
  ;;      τ
  ;;      mteff)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;      Γ_init
  ;;      (d-handle ()
  ;;                ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10))))))
  ;;              ((perform () getval unit) unit))
  ;;      τ
  ;;      mteff)
  ;;   τ)



  (judgment-holds
    (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
       Γ_init
       (λ () x unit 1)
       τ
       mteff)
    τ)


  (judgment-holds
    (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
       Γ_init
       (λ (some-eff) x unit 1)
       τ
       mteff)
    τ)

  (judgment-holds
    (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
       Γ_init
       ((d-handler mteff
                 ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10)))))))
        (λ (some-eff) x unit 1))
       τ
       mteff)
    τ)

  (let* ([effects
          (term ((times2 : (dup -> (∀ α (num -> mteff num))))
                 (times4 : (quad -> (∀ α (num -> (times2) num))))))]
         [h_times2
          (term ((dup (Λ α (λ mteff x num (λ mteff k (num -> mteff num) (k (mul x 2))))))))]
         [main
          (term ((perform mteff dup num) ((perform mteff dup num) 2)))])

    (test-equal
      (judgment-holds
        (⊢ ,effects Γ_init
           ((d-handler mteff ,h_times2)
            (λ (times2) x_1 unit ,main))
           τ
           mteff)
        τ)
      (term (num)))

    (test-->> ->effects
              (term (((d-handler mteff ,h_times2)
                      (λ (times2) x_1 unit ,main))
                     ()))
              (term (8 ())))
    )

  (let* ([effects
          (term ((times2 : (dup -> (∀ α (num -> () num))))
                 (times4 : (quad -> (∀ α (num -> () num))))))]
         [h_times2
          (term ((dup (Λ α (λ mteff x num (λ mteff k (num -> mteff num) (k (mul x 2))))))))]

         ;; calling other effects inside a handler
         [h_times4
          (term ((quad (Λ α (λ (times2) x num (λ (times2) k (num -> (times2) num)
                               (k ((perform mteff dup num) ((perform mteff dup num) x)))))))))]
         [main
          (term ((perform (times2) quad num) 2))])

    (test-equal
      (judgment-holds
        (⊢ ,effects Γ_init
           ((d-handler mteff ,h_times2)
            (λ (times2)
              x_1 unit
              ((d-handler (times2) ,h_times4)
               (λ (times2 times4) x_2 unit ,main))))
           τ
           mteff)
        τ)
      (term (num)))

    (test-->> ->effects
              (term (((d-handler mteff ,h_times2)
                      (λ (times2)
                        x_1 unit
                        ((d-handler (times2) ,h_times4)
                         (λ (times4) x_2 unit ,main))))
                     ()))
              (term (8 ()))))

  ;; make sure that dummy doesn't get called
  (test-->> ->effects
            (term ((d-handle (dup) h-dup
                             (d-handle (dummy) h-dummy
                                       (add ((perform () dup num) 2) 1))) ()))
            (term (5 ())))


  (define-term h-check
    ((Check (Λ α (λ () x α (λ () k (α -> () num)
                                   (if ((injl (injr x)) (injr (injr x)))
                                   (k (injr (injr x)))
                                   (blame (party "test")))))))))

  (test-match Effects h (term h-check))
  (test-->> ->effects
          (term ((d-handle (check) h-check ((perform () Check α) (t 123 (t (λ () x num false) 1)))) ()))
          (term ((blame (party "test")) ())))

  (test-->> ->effects
          (term ((d-handle (check) h-check ((perform () Check α) (t 123 (t (λ () x num true) 1)))) ()))
          (term (1 ())))
)
