#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(require "base.rkt")

(define-extended-language Effects Base
  (K ::= * (K -> K) eff lab)

  (ε ::= (effect ...))

  (τ ::= ....
         α
         (τ -> ε τ)
         (∀ α τ))

  (h ::= ((op f) ...))

  (f ::= (Λ α (λ ε x_1 τ_1 (λ ε k τ_2 e))))

  (e ::= ....
         (λ ε x τ e) ;; added epsilon here
         (e τ)
         (handle ε h e)
         (blame e))

  (v ::= ....
         (λ ε x τ e)
         (Λ α v)
         (handler ε h)
         (perform ε op τ))

  (E ::= ....
         (E τ)
         (handle ε h E)
         (blame E))

  (Σ ::= ((effect : (op -> τ) ...) ...))

  (α  ::= variable-not-otherwise-mentioned)
  (op ::= variable-not-otherwise-mentioned)

  ;; effect name
  (effect ::= variable-not-otherwise-mentioned)

  ;; to make continuation easy to write
  (k  ::= variable-not-otherwise-mentioned)

  #:binding-forms
  (Λ α v #:refers-to α)
  (λ ε x τ e #:refers-to x))

(define-metafunction Effects
  in-handler : op h -> boolean
  [(in-handler op ((op_1 f_1) ... (op f) (op_2 f_2) ... )) #true]
  [(in-handler _ _) #false])

(define-metafunction Effects
  find-op-in-handler : op h -> (τ f)
  [(find-op-in-handler
     op
     ((op_1 f_1) ... (op (Λ α (λ ε_1 x τ_1 (λ ε_2 k τ_2 e)))) (op_2 f_2) ...))
   (τ_2 (Λ α (λ ε_1 x τ_1 (λ ε_2 k τ_2 e))))])

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
  [(bop (o E e)) (bop E)]
  [(bop (o v E)) (bop E)]
  [(bop (if E e_1 e_2)) (bop E)]

  ;; not sure about this lol
  [(bop (E τ)) (bop E)]

  [(bop (handle ε ((op f) ...) E))
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
   ,(equal? (sort (term (effect_1 ...)) symbol<?)
            (sort (term (effect_2 ...)) symbol<?))])

(define-metafunction Effects
  types-equiv? : τ τ -> boolean

  ;; Base types
  [(types-equiv? num num) #true]
  [(types-equiv? bool bool) #true]
  [(types-equiv? unit unit) #true]
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
  [(types-equiv? (∀ α τ_1) (∀ α τ_2))
   (types-equiv? τ_1 τ_2)]

  ;; Fallback
  [(types-equiv? _ _) #false])

(define-judgment-form Effects
  #:mode (⊢_ops I I I O O O)
  #:contract (⊢_ops Σ Γ ((op f) ...) τ effect ε)

  [(where ((effect_list (∀ α (τ_1 -> ε τ_2))) ...) ((lookup-op Σ op) ...))

   (⊢_val Σ Γ f τ_f) ...

   (where ((∀ α_f (τ_1f -> ε_1f ((τ_2f -> ε_2f τ_3f) -> ε_3f τ_4f))) ...) (τ_f ...))

   (where (effect_out effect_rest ...) (effect_list ...))
   (where (τ_out τ_rest ...)          (τ_4f ...))
   (where (ε_out ε_rest ...)          (ε_3f ...))

   (side-condition
    ,(andmap (lambda (x) (equal? x (term effect_out))) (term (effect_rest ...))))
   (side-condition
    ,(andmap (lambda (x) (equal? x (term τ_out))) (term (τ_rest ...))))
   (side-condition
    ,(andmap (lambda (x) (equal? x (term ε_out))) (term (ε_rest ...))))

   --------------------------------------------------------- "T-E-Ops"
   (⊢_ops Σ Γ ((op f) ...) τ_out effect_out ε_out)]
)


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

  [---------------------- "T-E-Unit"
   (⊢_val Σ Γ unit unit)]

  [(⊢_val Σ Γ v_1 τ_1)
   (⊢_val Σ Γ v_2 τ_2)
   ------------------------------------ "T-E-Tuple"
   (⊢_val Σ Γ (t v_1 v_2) (t τ_1 τ_2))]

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

  [(⊢_ops Σ Γ h τ effect_0 ε_ops)
   (where (effect_1 ...) ε_ops)
   (side-condition (term (same-effects? ε ε_ops)))
   ----------------------------------------- "T-E-Handler"
   (⊢_val Σ Γ (handler ε h)
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
   (⊢ Σ Γ e_2 τ_3 ε)

   (side-condition (term (types-equiv? τ_1 τ_3)))
   (side-condition (term (same-effects? ε_0 ε)))
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

  [(⊢ Σ Γ e_1 bool ε)
   (⊢ Σ Γ e_2 τ ε)
   (⊢ Σ Γ e_3 τ ε)
   ----------------------------- "T-If"
   (⊢ Σ Γ (if e_1 e_2 e_3) τ ε)]

  ;; N-ary Operator Rule
  [(where ((τ_arg ...) τ_out) (op-type o))
   (⊢ Σ Γ e τ_arg ε) ...
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
   (⊢ Σ Γ e_2 τ ε)
   ------------------------- "T-Set"
   (⊢ Σ Γ (set e_1 e_2) unit ε)]

  [(⊢ Σ Γ e_1 τ_1 ε)
   (⊢ Σ Γ e_2 τ_2 ε)
   ---------------------------------- "T-E-Tuple"
   (⊢ Σ Γ (t e_1 e_2) (t τ_1 τ_2) ε)]

  [(⊢_ops Σ Γ h τ effect ε_1)
   (where (effect_0 ... ) ε_1)
   (⊢ Σ Γ e τ ε)
   (side-condition (term (same-effects? ε (effect effect_0 ...))))
   --------------------------------- "T-Handle"
   (⊢ Σ Γ (handle ε h e) τ ε)]
)

;; during evaluation we can ignore types and effects
;; just inherit reduction rules from base
(define ->effects
  (extend-reduction-relation ->base Effects
    [==> ((λ ε x τ e) v)
         (substitute e x v)
         APP-EFFECT]

    [==> ((Λ α v) τ)
         (substitute v α τ)
         TAPP]

    [==> ((handler ε h) v)
         (handle ε h (v unit))
         HANDLER-VALUE]

    [==> (handle ε h v)
         v
         HANDLE-VALUE]

    [==> (handle ε h (in-hole E ((perform ε_1 op τ) v)))
         (((f τ) v) e)

         (side-condition (term (unhandled op E)))
         (side-condition (term (in-handler op h)))
         (where (τ_2 f) (find-op-in-handler op h))
         (where e (λ y (substitute τ_2 α τ) (handle ε h (in-hole E y))))
         HANDLE-OP]

    with
    [(--> ((in-hole E before) σ) ((in-hole E after) σ))
     (==> before after)]))

(define-term Γ_init ())
(define-term mteff ())

(module+ test
  (define-term h-dup ((dup (Λ α (λ () x α (λ () k α (k (add x x)))))) ))
  (define-term h-get ((get (Λ α (λ () x α (λ () k α (λ () s num ((k s) s))))))))
  (define-term h-set ((set (Λ α (λ () x α (λ () k α (λ () s num ((k x) s))))))))

  (define-term h-dummy ((dummy (Λ α (λ () x α (λ () k α (k x)))))))

  (test-match Effects
    ((op f) ...)
    (term ((dup (Λ α (λ () x α (λ () k α (k x))))))))

  (test-match Effects
    h (term h-dup))

  (test-match Effects
    (handle ε h E)
    (term (handle (dup) h-dup (add hole 1))))

  (test-match Effects
    (handle ε h (in-hole (add hole 1) ((perform op τ) v)))
    (term (handle (dup) h-dup (add ((perform op τ) v) 1))))

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
  ;;          (handler () ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num)
  ;;                                                             (k 10)))))))
  ;;          τ)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;      Γ_init
  ;;      ((handler () ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10)))))))
  ;;       (perform () getval unit))
  ;;      τ
  ;;      mteff)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;      Γ_init
  ;;      ((handler () ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10)))))))
  ;;       (λ (some-eff) y unit ((perform () getval unit) unit)))
  ;;      τ
  ;;      mteff)
  ;;   τ)

  ;; (judgment-holds
  ;;   (⊢ ((some-eff : (getval -> (∀ α (unit -> () num)))))
  ;;      Γ_init
  ;;      (handle ()
  ;;              ((getval (Λ α (λ mteff x unit (λ mteff k (num -> () num) (k 10))))))
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
       ((handler mteff
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
           ((handler mteff ,h_times2)
            (λ (times2) x_1 unit ,main))
           τ
           mteff)
        τ)
      (term (num)))

    (test-->> ->effects
              (term (((handler mteff ,h_times2)
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
           ((handler mteff ,h_times2)
            (λ (times2)
              x_1 unit
              ((handler (times2) ,h_times4)
               (λ (times2 times4) x_2 unit ,main))))
           τ
           mteff)
        τ)
      (term (num)))

    (test-->> ->effects
              (term (((handler mteff ,h_times2)
                      (λ (times2)
                        x_1 unit
                        ((handler (times2) ,h_times4)
                         (λ (times4) x_2 unit ,main))))
                     ()))
              (term (8 ()))))

  ;; make sure that dummy doesn't get called
  (test-->> ->effects
            (term ((handle (dup) h-dup
                           (handle (dummy) h-dummy
                                   (add ((perform () dup num) 2) 1))) ()))
            (term (5 ())))


  (define-term h-check
    ((Check (Λ α (λ () x α (λ () k α
                                   (if ((injl (injr x)) (injr (injr x)))
                                   (k (injr (injr x)))
                                   (blame 111))))))))

  (test-match Effects h (term h-check))
  (test-->> ->effects
          (term ((handle (check) h-check ((perform () Check α) (t 123 (t (λ () x num false) 1)))) ()))
          (term ((blame 111) ())))

  (test-->> ->effects
          (term ((handle (check) h-check ((perform () Check α) (t 123 (t (λ () x num true) 1)))) ()))
          (term (1 ())))
)
