#lang racket

(provide CompilerLang compile run-compiler run-type translate-type wrap compile-and-run)

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

;; Every compiled function may execute a contract check.  Translate recursively,
;; including function types nested inside tuples and references.
(define-metafunction CompilerLang
  translate-type : C:τ -> E:τ
  [(translate-type num) num]
  [(translate-type bool) bool]
  [(translate-type unit) unit]
  [(translate-type (t C:τ_1 C:τ_2))
   (t (translate-type C:τ_1) (translate-type C:τ_2))]
  [(translate-type (ref C:τ)) (ref (translate-type C:τ))]
  [(translate-type (C:τ_1 -> C:τ_2))
   ((translate-type C:τ_1) -> (con) (translate-type C:τ_2))])

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
            ;; remember to evaluate the contract expression first
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
   (where E:x ,(term C:x))
   ------------------------------------------------------------------ "C-Mon-Tuple"
   (compile C:Γ
            (mon C:k C:l C:j (t C:κ_1 C:κ_2) C:e)
            (t C:τ_1 C:τ_2)
            ((λ (con) E:x E:τ (t E:e_1 E:e_2)) E:e_3))]
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

;; The handler itself is pure: it runs predicate computations under a fresh
;; deep wrapper, and its resumed continuation already handles further checks.
;; perform's annotation is the *tail* of the effect row, hence ().
(define-term h-check
  ((effcheck
     (Λ α (λ () x (t party (t (α -> (con) bool) α))
       (λ () k (α -> () β)
         (if ((w bool) (λ (con) ignored unit ((injl (injr x)) (injr (injr x)))))
             (k (injr (injr x)))
             (blame (injl x)))))))))

(define-term wrap
  (μ w (∀ β ((unit -> (con) β) -> () β))
    (Λ β (λ () f (unit -> (con) β) ((d-handler () h-check) f)))))

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

  (define pp (term (((wrap (translate-type (run-type ,p)))
                     (λ (con) _ unit (run-compiler ,p))) ())))

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

;; Semantic check: run the source program with ->contracts and the compiled
;; program with ->effects, and compare the observable outcomes.
;;   - blame in source  <=> blame in target
;;   - first-order values (num, bool, unit, tuples of them) must be equal
;;   - higher-order values are only required to be values on both sides
(define (observe result #:source? [source? #f])
  ;; Source blame may remain in an evaluation context; target blame is an
  ;; abortive terminal result, and handler bodies contain latent blame terms.
  (define (source-blame? e)
    (or (match e [`(blame ,_ ,_) #t] [_ #f])
        (and (list? e) (ormap source-blame? e))))
  (define (first-order? v)
    (match v
      [(? number?) #t]
      ['true #t] ['false #t] ['unit #t]
      [`(t ,a ,b) (and (first-order? a) (first-order? b))]
      [_ #f]))
  (match result
    [(list (list e _))
     (cond
       [(or (and source? (source-blame? e))
            (match e [`(blame ,_ ,_) #t] [`(blame ,_) #t] [`(error ,_) #t] [_ #f]))
        'blame]
       [(first-order? e) e]
       [else 'procedure])]
    [_ (list 'unexpected result)]))

(define (compile-check-semantics p)
  (define source (apply-reduction-relation* ->contracts (term (,p ()))))
  (define target (compile-and-run p))
  (test-equal (observe target) (observe source #:source? #t))
  (observe source #:source? #t))


(module+ test
  (require rackunit)

  ;; Check the compiler's type translation against the target judgment, not
  ;; just the shape of emitted syntax.  The operation has an empty row tail;
  ;; its declared effect supplies con at the call site.
  (define Σ-check
    (term ((con : (𝒞 -> (∀ α ((t party (t (α -> (con) bool) α)) -> () α)))))))
  (check-equal? (term (translate-type (ref (t (num -> bool) (unit -> (num -> num))))))
                (term (ref (t (num -> (con) bool)
                              (unit -> (con) (num -> (con) num))))))
  (for ([example (in-list
                  (list (list (term 7) (term num))
                        (list (term (λ f (num -> bool) f))
                              (term ((num -> (con) bool) -> (con) (num -> (con) bool))))
                        (list (term (μ f (num -> num) (λ x num (f x))))
                              (term (num -> (con) num)))
                        (list (term (mon k l j (flat (λ x num (pos? x))) 7))
                              (term num))
                        (list (term (mon k l j (t (flat (λ x num true))
                                                       (flat (λ b bool b))) (t 1 true)))
                              (term (t num bool)))
                        (list (term (mon k l j ((flat (λ x num true)) ->
                                                (flat (λ x num true)))
                                         (λ x num x)))
                              (term (num -> (con) num)))
                        (list (term ((mon k l j ((flat (λ x num true)) ->i y
                                                  (flat (λ r num (gt r y))))
                                           (λ x num (add x 1))) 2))
                              (term num))))])
    (match-define (list source expected) example)
    (define target (term (run-compiler ,source)))
    (check-not-false (member expected (judgment-holds (⊢ ,Σ-check () ,target τ (con)) τ))
                     (format "compiled target: ~s" source)))

  ;; Directly verify the operation clause in the recursive wrapper environment.
  (check-true
   (judgment-holds
    (⊢_ops/mod deep ,Σ-check
               ((w (∀ β ((unit -> (con) β) -> () β)))) h-check β con ())))
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


  ;; Each monitor form has one applicable compilation rule.
  (define-syntax-rule (check-unique-compilation e)
    (test-equal (length (judgment-holds (compile () e C:τ E:e)
                                       (C:τ E:e)))
                1))
  (check-unique-compilation (mon k l j (flat (λ x num true)) 1))
  (check-unique-compilation
   (mon k l j ((flat (λ x num true)) -> (flat (λ x num true)))
        (λ x num x)))
  (check-unique-compilation
   (mon k l j ((flat (λ x num true)) ->i y (flat (λ x num (eq x y))))
        (λ x num x)))
  (check-unique-compilation
   (mon k l j (t (flat (λ x num true)) (flat (λ x num true))) (t 1 2)))

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
    #:trace-enabled false)

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

  ;; semantic checks: source and compiled program must agree
  (define-syntax-rule (check-semantics p expected)
    (test-equal (compile-check-semantics (term p)) (term expected)))

  (check-semantics (add 1 2) 3)
  (check-semantics (mon k l j (flat (λ x num (zero? x))) 0) 0)
  (check-semantics (mon k l j (flat (λ x num (zero? x))) 1) blame)
  (check-semantics (add (mon k l j (flat (λ x num true)) 2) 2) 4)
  (check-semantics (add (mon k l j (flat (λ x num false)) 2) 2) blame)
  (check-semantics (mon k l j (t (flat (λ x num true)) (flat (λ x num true))) (t 1 2))
                   (t 1 2))
  (check-semantics (mon k l j (t (flat (λ x num true)) (flat (λ x num (zero? x)))) (t 1 2))
                   blame)

  ;; function contracts
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) -> (flat (λ x num true)))
                         (λ x num (add x 1)))
                    10)
                   11)
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) -> (flat (λ x num false)))
                         (λ x num (add x 1)))
                    10)
                   blame)
  (check-semantics ((mon k l j
                         ((flat (λ x num (pos? x))) -> (flat (λ x num true)))
                         (λ x num (add x 1)))
                    -5)
                   blame)
  (check-semantics (mon k l j
                        ((flat (λ x num true)) -> (flat (λ x num true)))
                        (λ x num (add x 1)))
                   procedure)
  ;; higher-order: contract on the argument function
  (check-semantics ((mon k l j
                         (((flat (λ x num (pos? x))) -> (flat (λ x num true)))
                          -> (flat (λ x num true)))
                         (λ g (num -> num) (g 3)))
                    (λ x num (mul x 2)))
                   6)
  (check-semantics ((mon k l j
                         (((flat (λ x num true)) -> (flat (λ x num (pos? x))))
                          -> (flat (λ x num true)))
                         (λ g (num -> num) (g 3)))
                    (λ x num (sub 0 x)))
                   blame)
  ;; curried: range is a function contract
  (check-semantics (((mon k l j
                          ((flat (λ x num true))
                           -> ((flat (λ x num true)) -> (flat (λ x num (gt x 0)))))
                          (λ a num (λ b num (add a b))))
                     1) 2)
                   3)
  (check-semantics (((mon k l j
                          ((flat (λ x num true))
                           -> ((flat (λ x num true)) -> (flat (λ x num (gt x 0)))))
                          (λ a num (λ b num (add a b))))
                     1) -5)
                   blame)

  ;; dependent contracts
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) ->i y (flat (λ x num (eq (sub x y) 1))))
                         (λ x num (add x 1)))
                    10)
                   11)
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) ->i y (flat (λ x num (zero? (sub x y)))))
                         (λ x num (add x 1)))
                    10)
                   blame)
  (check-semantics ((mon k l j
                         ((flat (λ x num (pos? x))) ->i y (flat (λ x num (gt x y))))
                         (λ x num (add x 1)))
                    -3)
                   blame)
  ;; the dependent variable shadows / coincides with the lambda parameter name
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) ->i x (flat (λ r num (gt r x))))
                         (λ x num (mul x 2)))
                    5)
                   10)
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) ->i x (flat (λ r num (gt r x))))
                         (λ x num (mul x 2)))
                    -5)
                   blame)
  ;; dependent contract with a function-contract range
  (check-semantics (((mon k l j
                          ((flat (λ x num true))
                           ->i y ((flat (λ x num true)) -> (flat (λ r num (gt r y)))))
                          (λ a num (λ b num (add a b))))
                     1) 2)
                   3)
  (check-semantics (((mon k l j
                          ((flat (λ x num true))
                           ->i y ((flat (λ x num true)) -> (flat (λ r num (gt r y)))))
                          (λ a num (λ b num (add a b))))
                     1) -2)
                   blame)
  ;; nested monitors
  (check-semantics ((mon k l j
                         ((flat (λ x num true)) -> (flat (λ x num (lt x 100))))
                         (mon k l j
                              ((flat (λ x num (pos? x))) -> (flat (λ x num true)))
                              (λ x num (mul x 10))))
                    5)
                   50)
)
