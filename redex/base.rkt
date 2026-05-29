#lang racket

(provide (all-defined-out))
(require redex/reduction-semantics)

(define-language Base
  (e ::= v (μ x τ e)
         (t e e) (e e)
         (injl e) (injr e)
         (o e ...)
         (if e e e)
         (new e) (get e) (set e e))

  (o ::= add sub mul div pow
         and or not
         pos? neg? zero?
         lt lte gt gte eq neq)

  (v ::= n b x (λ x τ e) (t v v) unit loc)

  (E ::= hole
         (E e) (v E)
         (t E e) (t v E)
         (injl E) (injr E)
         (o v ... E e ...)
         (if E e e)
         (new E) (get E) (set E e) (set v E))

  (τ ::= bool num (τ -> τ) (t τ τ) unit (ref τ))

  (n ::= integer)
  (b ::= true false)
  (x ::= variable-not-otherwise-mentioned)

  (loc ::= variable-not-otherwise-mentioned)

  (Γ ::= ((x τ) ...))
  (σ ::= ((loc v) ...))

  #:binding-forms
  (λ x τ e #:refers-to x)
  (μ x τ e #:refers-to x))

(define-metafunction Base
  extend : Γ x τ -> Γ
  [(extend ((x_1 τ_1) ...) x τ)
   ((x τ) (x_1 τ_1) ...)])

(define-metafunction Base
  lookup : Γ x -> τ
  [(lookup ((x_1 τ_1) ... (x τ) (x_2 τ_2) ...) x) τ])

;; Memory Store
(define-metafunction Base
  extend-store : σ loc v -> σ
  [(extend-store ((loc_1 v_1) ...) loc v)
   ((loc v) (loc_1 v_1) ...)])

(define-metafunction Base
  lookup-store : σ loc -> v
  [(lookup-store ((loc_1 v_1) ... (loc v) (loc_2 v_2) ...) loc) v])

(define-metafunction Base
  update-store : σ loc v -> σ
  [(update-store ((loc_1 v_1) ... (loc v_old) (loc_2 v_2) ...) loc v_new)
   ((loc_1 v_1) ... (loc v_new) (loc_2 v_2) ...)])

(define-metafunction Base
  op-type : o -> ((τ ...) τ)
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

(define-metafunction Base
  delta : o v ... -> v
  [(delta pos? n)       ,(if (>= (term n) 0) (term true) (term false))]
  [(delta neg? n)       ,(if (< (term n) 0) (term true) (term false))]
  [(delta zero? 0)      true]
  [(delta zero? n)      false]
  [(delta add n_1 n_2)  ,(+ (term n_1) (term n_2))]
  [(delta sub n_1 n_2)  ,(- (term n_1) (term n_2))]
  [(delta mul n_1 n_2)  ,(* (term n_1) (term n_2))]
  [(delta div n_1 n_2)  ,(/ (term n_1) (term n_2))]
  [(delta pow n_1 n_2)  ,(expt (term n_1) (term n_2))]
  [(delta gt n_1 n_2)   ,(if (> (term n_1) (term n_2)) (term true) (term false))]
  [(delta gte n_1 n_2)  ,(if (>= (term n_1) (term n_2)) (term true) (term false))]
  [(delta lt n_1 n_2)   ,(if (< (term n_1) (term n_2)) (term true) (term false))]
  [(delta lte n_1 n_2)  ,(if (<= (term n_1) (term n_2)) (term true) (term false))]
  [(delta eq? n_1 n_2)  ,(if (= (term n_1) (term n_2)) (term true) (term false))]
  [(delta neq? n_1 n_2) ,(if (not (= (term n_1) (term n_2))) (term true) (term false))]
  [(delta and b_1 b_2)  ,(if (and (term n_1) (term n_2)) (term true) (term false))]
  [(delta or b_1 b_2)   ,(if (or (term n_1) (term n_2)) (term true) (term false))]
  [(delta not b_1)      ,(if (term b_1) (term true) (term false))])

(define-judgment-form Base
  #:mode (⊢ I I O)
  #:contract (⊢ Γ e τ)

  [----------- "T-Num"
   (⊢ Γ n num)]

  [----------- "T-Bool"
   (⊢ Γ b bool)]

  [----------- "T-Unit"
   (⊢ Γ unit unit)]

  ;; Locations type-check identically to variables
  [(where τ (lookup Γ x))
   ---------------------- "T-Var/Loc"
   (⊢ Γ x τ)]

  [(⊢ Γ e num)
   ----------------------------- "T-Zero"
   (⊢ Γ (zero? e) bool)]

  [(⊢ (extend Γ x τ_1) e τ_2)
   -------------------------------- "T-Lambda"
   (⊢ Γ (λ x τ_1 e) (τ_1 -> τ_2))]

  [(⊢ Γ e_1 (τ_1 -> τ_2))
   (⊢ Γ e_2 τ_1)
   -------------------------------- "T-App"
   (⊢ Γ (e_1 e_2) τ_2)]

  [(⊢ Γ e (t τ_1 τ_2))
   ----------------------------- "T-Proj-L"
   (⊢ Γ (injl e) τ_1)]

  [(⊢ Γ e (t τ_1 τ_2))
   ----------------------------- "T-Proj-R"
   (⊢ Γ (injr e) τ_2)]

  [(⊢ Γ e_1 bool)
   (⊢ Γ e_2 τ)
   (⊢ Γ e_3 τ)
   ----------------------------- "T-If"
   (⊢ Γ (if e_1 e_2 e_3) τ)]

  ;; N-ary Operator Rule
  [(where ((τ_arg ...) τ_out) (op-type o))
   (⊢ Γ e τ_arg) ...
   -------------------------------------- "T-Op"
   (⊢ Γ (o e ...) τ_out)]

  ;; Stateful Typing Rules
  [(⊢ Γ e τ)
   ------------------------- "T-New"
   (⊢ Γ (new e) (ref τ))]

  [(⊢ Γ e (ref τ))
   ------------------------- "T-Get"
   (⊢ Γ (get e) τ)]

  [(⊢ Γ e_1 (ref τ))
   (⊢ Γ e_2 τ)
   ------------------------- "T-Set"
   (⊢ Γ (set e_1 e_2) unit)]

  ;; order matters, put this later
  [(⊢ Γ e_1 τ_1)
   (⊢ Γ e_2 τ_2)
   ------------------------------ "T-Tuple"
   (⊢ Γ (t e_1 e_2) (t τ_1 τ_2))])

(define ->base
  (reduction-relation Base
    [==> ((λ x τ e) v)
         (substitute e x v)
         App]

    [==> (μ x τ e)
         (substitute e x (μ x τ e))
         Fix]

    [==> (injl (t v_1 v_2)) v_1
         Proj-Left]

    [==> (injr (t v_1 v_2)) v_2
         Proj-Right]

    [==> (if true e_1 e_2) e_1
         If-True]

    [==> (if false e_1 e_2) e_2
         If-False]

    [==> (o v ...)
         (delta o v ...)
         BASE-OP]

    ;; states
    [--> ((in-hole E (new v)) σ)
         ((in-hole E loc_new) (extend-store σ loc_new v))
         (where loc_new ,(variable-not-in (term σ) 'loc))
         New]

    [--> ((in-hole E (get loc)) σ)
         ((in-hole E v) σ)
         (where v (lookup-store σ loc))
         Get]

    [--> ((in-hole E (set loc v)) σ)
         ((in-hole E unit) (update-store σ loc v))
         Set]

    with
    [(--> ((in-hole E before) σ) ((in-hole E after) σ))
     (==> before after)]))

(module+ test
  (test-->> ->base
            (term ( (add 1 2) () ))
            (term ( 3 () )))

  (test-->> ->base
            (term ( (injl (t (add 1 2) 4)) () ))
            (term ( 3 () )))

  (test-->> ->base
            (term ( ((λ x (ref num)
                       ((λ _ unit (get x))
                        (set x (add (get x) 5))))
                     (new 10))
                    () ))
            (term ( 15 ((loc 15)) )))

  (test-equal (judgment-holds (⊢ () (add 1 2) τ) τ)
              '(num))

  (test-results))
