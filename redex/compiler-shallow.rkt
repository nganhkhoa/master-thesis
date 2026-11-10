#lang racket

(provide compile run-compiler wrap compile-and-run)

(require redex/reduction-semantics)

;; (require "base.rkt")
(require "contracts.rkt")
(require "effects.rkt")

;; State requests are source forms for this state-aware shallow compiler.
;; Keep the extension local rather than changing the other contract models.
(define-extended-language StateContracts Contracts
  (e ::= .... (GetState) (SetState e)
         (GetState n) (SetState n e)))

(define-union-language CompilerLang (C: StateContracts) (E: Effects))

(define-metafunction CompilerLang
  extend : C:Γ C:x C:τ -> C:Γ
  [(extend ((C:x_1 C:τ_1) ...) C:x C:τ)
   ((C:x C:τ) (C:x_1 C:τ_1) ...)])

(define-metafunction CompilerLang
  lookup : C:Γ C:x -> C:τ
  [(lookup ((C:x_1 C:τ_1) ... (C:x C:τ) (C:x_2 C:τ_2) ...) C:x) C:τ])

;; A source function may perform contract checks when called.  Translate
;; recursively: target arrows carry their latent effect explicitly.
(define-metafunction CompilerLang
  translate-type : C:τ -> E:τ
  [(translate-type (C:τ_1 -> C:τ_2))
   ((translate-type C:τ_1) -> (con) (translate-type C:τ_2))]
  [(translate-type (t C:τ_1 C:τ_2))
   (t (translate-type C:τ_1) (translate-type C:τ_2))]
  [(translate-type (ref C:τ)) (ref (translate-type C:τ))]
  [(translate-type num) num]
  [(translate-type bool) bool]
  [(translate-type unit) unit])

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
  #:contract (compile C:Γ any C:τ E:e)

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

  ;; State operations include con in their tail: T-E-Perform prepends the
  ;; operation label itself, so their total effect is (state con).
  [----------------------------- "C-GetState"
   (compile C:Γ (GetState) num
            ((perform (con) getState num) unit))]

  [(compile C:Γ C:e num E:e)
   ----------------------------- "C-SetState"
   (compile C:Γ (SetState C:e) unit
            ((perform (con) setState num) E:e))]

  ;; Indexed requests are distinct operations, not keys in a runtime store.
  [(where E:op ,(string->symbol (format "getState~a" (term C:n))))
   ----------------------------- "C-GetState-Indexed"
   (compile C:Γ (GetState C:n) num
            ((perform (con) E:op num) unit))]

  [(compile C:Γ C:e num E:e)
   (where E:op ,(string->symbol (format "setState~a" (term C:n))))
   ----------------------------- "C-SetState-Indexed"
   (compile C:Γ (SetState C:n C:e) unit
            ((perform (con) E:op num) E:e))]

  ;; [(where E:loc ,(term C:loc))
  ;;  ------------------------------------ "C-LOC"
  ;;  (compile C:Γ C:loc (ref τ) E:loc)]

  [(where C:Γ_new (extend C:Γ C:x C:τ_1))
   (compile C:Γ_new C:e C:τ_2 E:e_body)
   (where E:x ,(term C:x))
   (where E:τ_1 (translate-type C:τ_1))
   ------------------------------------------------------------------------ "C-Lambda"
   (compile C:Γ (λ C:x C:τ_1 C:e) (C:τ_1 -> C:τ_2) (λ (con) E:x E:τ_1 E:e_body))]

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
   ----------------------------------------------------- "C-Mon-Flat"
   (compile C:Γ (mon C:k C:l C:j (flat C:e_1) C:e_2) C:τ
            ((perform () 𝒞 E:τ) (t (party E:p) (t E:e_1 E:e_2))))]

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
            (E:e_4 E:e_compiled))]

  ;; Preserve substitution of the dependent argument in the source contract:
  ;; every occurrence of x_arg in κ_2 receives its own monitored argument.
  ;; Binding x_arg once would incorrectly share a check.
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
   ----------------------------------------------------------------------- "C-Mon-Dep-Complex"
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
            ((λ (con) C:x E:τ (t E:e_1 E:e_2)) E:e_3))]
)

(define-metafunction CompilerLang
  run-compiler : C:e -> E:e

  [(run-compiler C:e_in) E:e_out
   (where (E:e_out) ,(judgment-holds (compile () C:e_in C:τ E:e_target)
                                      E:e_target))])

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
(define-term mteff ())
(define-term genericeff ( con )) ;; add to all expression

;; H = μh. s-handler {𝒞 ↦ ... h (λ_. if predicate then k value else blame)}.
;; A shallow continuation does not reinstall H; the clause does so around the
;; whole conditional, including both predicate evaluation and resumption.
(define-term h-check
  ((effcheck
     (Λ α (λ () x (t party (t (α -> (con) bool) α))
       (λ () k (α -> (con) β)
         (h (λ (con) _ unit
           (if ((injl (injr x)) (injr (injr x)))
               (k (injr (injr x)))
               (blame (injl x)))))))))))

;; The recursive handler consumes a check-effectful thunk and returns β in
;; the empty ambient effect. β is bound by wrap, not by the operation clause.
(define-term H-check
  (μ h ((unit -> (con) β) -> () β) (s-handler () h-check)))

(define-term wrap
  (Λ β (λ () f (unit -> (con) β) (H-check f))))

(define (compile-and-run p #:trace-enabled [trace-enabled false] #:trace-print [trace-print false])
  (define (abbreviate-term t)
    (match t
      ;; [`(𝒞 (Λ ,alpha (λ ,eff1 ,x ,alpha2 (λ ,eff2 ,k ,alpha3 (if ,cond ,then ,else)))))
      ;;  'HandlerC]

      [`(𝒞 ,handler-body) 'Handler𝒞]

      [`((perform ,_ ,𝒞 ,_) (,_ ,e1 ,e2))
       (string->symbol
        (format "EffectCheck(~a,~a)"
                (abbreviate-term e1)
                (abbreviate-term e2)))]

      ;; Recursively walk down all other AST nodes
      [(list xs ...) (map abbreviate-term xs)]

      ;; Leave atoms (numbers, symbols) as they are
      [_ t]))

  (define (my-pp term)
    (pretty-format (abbreviate-term term)))

  (define pp (term (((wrap unit) (λ genericeff _ unit (run-compiler ,p))) ())))

  (if trace-enabled
      (let [(traces (dynamic-require 'redex/gui 'traces))
            (reduction-steps-cutoff (dynamic-require 'redex/gui 'reduction-steps-cutoff))]
        (reduction-steps-cutoff 100)
        (traces ->effects pp #:pp my-pp)
        (traces ->contracts (term (,p ()))))
       null)

  (if trace-print
    (let ()
      ;; A robust, headless replacement for `build-trace`
      (define (print-trace rel initial-term [cutoff 100])
        (define seen (make-hash))
        (define count 0)

        (define (explore t)
          (unless (or (hash-has-key? seen t) (>= count cutoff))
            (hash-set! seen t #t)
            (set! count (add1 count))

            ;; Get all reductions for the current term
            (define steps (apply-reduction-relation/tag-with-names rel t))

            ;; Print the transitions exactly like the nested `for` loop did
            (for ([step (in-list steps)])
              (match-define (list label next-t) step)
              (printf "  --[~a]--> ~s\n" label next-t))

            ;; Recursively visit the children
            (for ([step (in-list steps)])
              (explore (second step)))))

        (explore initial-term))

      (printf "Contracts Execution Trace of ~s\n" p)
      (print-trace ->contracts (term (,p ())) 100)
      (printf "END Contracts Execution Trace\n\n")

      (printf "Effects Execution Trace of ~s\n" pp)
      (print-trace ->effects pp 100)
      (printf "END Effects Execution Trace\n"))

    null)

  (apply-reduction-relation* ->effects pp))


(module+ test
  (require rackunit)

  ;; Check real target derivations, not just the shape of generated terms.
  (define Σ-check
    (term ((con : (𝒞 -> (∀ α ((t party (t (α -> (con) bool) α)) -> () α)))))))
  (for ([case (in-list
               (list (list (term 7) (term num))
                     (list (term (λ f (num -> bool) (f 1)))
                           (term ((num -> (con) bool) -> (con) bool)))
                     (list (term (mon k l j (flat (λ x num true)) 7)) (term num))
                     (list (term (mon k l j (t (flat (λ x num true))
                                               (flat (λ x bool true)))
                                      (t 1 true))) (term (t num bool)))
                     (list (term (mon k l j ((flat (λ x num true)) ->
                                              (flat (λ x bool true)))
                                      (λ x num true)))
                           (term (num -> (con) bool)))))])
    (define compiled (term (run-compiler ,(first case))))
    (check-true (judgment-holds (⊢_check ,Σ-check () ,compiled ,(second case) (con)))
                (format "target typing: ~s" compiled)))

  (define Σ-state
    (term ((con : (𝒞 -> (∀ α ((t party (t (α -> (con) bool) α)) -> () α))))
           (state : (getState -> (∀ α (unit -> () num)))
                    (setState -> (∀ α (num -> () unit)))
                    (getState1 -> (∀ α (unit -> () num)))
                    (setState1 -> (∀ α (num -> () unit)))))))
  (for ([case (in-list (list (list (term (GetState)) (term num))
                             (list (term (SetState 3)) (term unit))
                             (list (term (GetState 1)) (term num))
                             (list (term (SetState 1 3)) (term unit))))])
    (define compiled (term (run-compiler ,(first case))))
    (check-true (judgment-holds
                 (⊢_check ,Σ-state () ,compiled ,(second case) (state con)))))

  ;; The handler's continuation result type is independent of the operation's
  ;; polymorphic argument.  Its free β comes from the outer wrapper.
  (define check-clause (second (first (term h-check))))
  (check-not-false
   (member (term (∀ α ((t party (t (α -> (con) bool) α)) -> ()
                        ((α -> (con) β) -> () β))))
           (judgment-holds
            (⊢_val ,Σ-check ((h ((unit -> (con) β) -> () β)))
                   ,check-clause τ) τ)
           (lambda (a b) (alpha-equivalent? Effects a b))))
  (check-equal? (term (translate-type (ref (t (num -> bool) unit))))
                (term (ref (t (num -> (con) bool) unit))))
  ;; Exact blamed party: flat and range blame the provider; domain blames
  ;; the client.  Passing checks resume with the original value.
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
    (test-equal (compile-and-run (first case)) (list (second case))))

  ;; Each monitor form has exactly one compiler derivation, including nested
  ;; contracts and tuples whose component types differ.
  (for ([source (in-list
                 (list (term (mon k l j (flat (λ x num true)) 1))
                       (term (mon k l j ((flat (λ x num true)) ->
                                         (flat (λ x num true)))
                                  (λ x num x)))
                       (term (mon k l j ((flat (λ x num true)) ->i y
                                         (flat (λ x num (eq x y))))
                                  (λ x num x)))
                       (term (mon k l j (t (flat (λ x num true))
                                           (flat (λ x bool true)))
                                  (t 1 true)))))])
    (test-equal (length (judgment-holds (compile () ,source C:τ E:e) E:e)) 1))

  ;; Generated wrapper binders must not capture variables in contracts.
  (test-equal
   (compile-and-run
    (term (((λ x num
              (mon k l j ((flat (λ z num (eq z x))) ->
                          (flat (λ z num true)))
                   (λ z num z))) 7) 7)))
   (term ((7 ()))))


  (compile-expect 1 1)

  (compile-expect true true)

  (compile-expect (λ x num 1)
                  (λ (con) x num 1))

  (compile-expect (λ x num x)
                  (λ (con) x num x))

  (compile-expect (t (λ x num x) 1)
                  (t (λ (con) x num x) 1))

  (compile-expect (injl (t (λ x num x) 1))
                  (injl (t (λ (con) x num x) 1)))

  (compile-expect (add 1 2)
                  (add 1 2))

  (compile-expect (mon k l j (flat (λ x num (zero? x))) 0)
                  ((perform () effcheck num) (t (party "k") (t (λ (con) x num (zero? x)) 0))))

  ;; (compile-expect
  ;;   (mon k l j
  ;;        ((flat (λ x num true)) -> (flat (λ x num false)))
  ;;        (λ x num (add x 1)))
  ;;   (λ x num ((perform genericeff effcheck num)
  ;;             (t (λ x num false)
  ;;                ((λ x num (add x 1))
  ;;                 ((perform genericeff effcheck num)
  ;;                  (t (λ x num true) x)))))))

  ;; (compile-expect
  ;;   (mon k l j
  ;;        ((flat (λ x num true)) ->i y (flat (λ x num (lt y x))))
  ;;        (λ x num (add x 1)))
  ;;   (λ arg num ((perform genericeff effcheck num)
  ;;               (t (λ x num (lt ((perform genericeff effcheck num) (t (λ x num true) arg)) x))
  ;;                  ((λ x num (add x 1))
  ;;                   ((perform genericeff effcheck num)
  ;;                    (t (λ x num true) arg)))))))

  (compile-expect
    (mon k l j (t (flat (λ x num true)) (flat (λ x num true))) (t 1 2))
    ((λ (con) x (t num num)
       (t ((perform () 𝒞 num) (t (party "k") (t (λ (con) x num true) (injl x))))
          ((perform () 𝒞 num) (t (party "k") (t (λ (con) x num true) (injr x))))))
     (t 1 2)))

  (compile-and-run
    (term (mon k l j (flat (λ x num true)) (add 1 1)))
    #:trace-enabled false)

  (compile-and-run
    (term (add (mon k l j (flat (λ x num true)) 2) 2))
    #:trace-enabled false)

  (compile-and-run
    (term (mon k l j (t (flat (λ x num true)) (flat (λ x num true))) (t 1 2)))
    #:trace-enabled false)

  (compile-and-run
    (term ((mon k l j
                ((flat (λ x num true)) ->i y (flat (λ x num (eq (sub x y) 1))))
                (λ x num (add x 1)))
           10))
    #:trace-enabled false
    #:trace-print true)

  (compile-and-run
    (term ((λ y (num -> num) y) (λ x num (add x 1))))
    #:trace-enabled false)

  (compile-and-run
    (term (mon k l j
               #;((flat (λ x num true)) ->i y (flat (λ x num (zero? (sub x y)))))
               ((flat (λ x num true)) -> (flat (λ x num true)))
               ((λ x (num -> num) x) (λ x num (add x 1)))))
    #:trace-enabled false)


  (compile-and-run
    (term ((mon k l j
               ;; ((flat (λ x num true)) ->i y (flat (λ x num (eq (sub x y) 1))))
               ((flat (λ x num true)) -> (flat (λ x num true)))
               ((λ x (num -> num) x) (λ x num (add x 1))))
           10))
    #:trace-enabled false
    #:trace-print false)
)
