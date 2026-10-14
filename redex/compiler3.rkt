#lang racket

(provide compile)

(require redex/reduction-semantics)

;; (require "base.rkt")
(require "contracts.rkt")
(require "effects.rkt")

(define-union-language CompilerLang (C: ContractsHijack) (E: Effects))

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
            ((perform genericeff 𝒞 C:τ) (t E:e_1 E:e_2)))]

  [(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled) ;; get τ_1
   (where (C:x C:x_1) ,(variables-not-in (term (C:Γ C:e)) '(x x_1)))
   ;; (where C:Γ_new (extend C:Γ C:x C:τ_1))
   ;; (where C:Γ_f (extend C:Γ_new C:x_1 (C:τ_1 -> C:τ_2)))

   ;; (compile C:Γ_new (mon C:l C:k C:j C:κ_1 C:x) C:τ_1 E:e_1)
   ;; (compile C:Γ_f (mon C:k C:l C:j C:κ_2 (C:x_1 C:x)) C:τ_2 E:e_2)

   (compile C:Γ
            (λ C:x_1 (C:τ_1 -> C:τ_2)
              (λ C:x C:τ_1
                (mon C:k C:l C:j C:κ_2
                     (C:x_1 (mon C:l C:k C:j C:κ_1 C:x)))))
            ((C:τ_1 -> C:τ_2) -> (C:τ_1 -> C:τ_2))
            E:e_4)

   ;; (where E:e_3 (substitute E:e_2 C:x E:e_1))
   --------------------------------------------------------------- "C-Mon-Func"
   (compile C:Γ
            (mon C:k C:l C:j (C:κ_1 -> C:κ_2) C:e)
            (C:τ_1 -> C:τ_2)
            ;; remember to evaluate the contract expression first
            ;; ((λ C:x_1 (C:τ_1 -> C:τ_2) (λ C:x C:τ_1 E:e_3)) E:e_compiled))]
            (E:e_4 E:e_compiled))]

  ;; ((guard k l j (κ_1 ->i y κ_2) f) v)
  ;;   --> (mon k l j κ_2[y := (mon l j j κ_1 v)] (f (mon l k j κ_1 v)))
  ;; the indy-monitored argument is bound to y (with type τ_1) before
  ;; checking the range, so κ_2 is compiled in a context where y : τ_1
  [(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled) ;; get τ_1
   (where (C:x C:x_1) ,(variables-not-in (term (C:Γ C:e C:κ_1 C:κ_2 C:x_arg)) '(x x_1)))

   (compile C:Γ
            (λ C:x_1 (C:τ_1 -> C:τ_2)
              (λ C:x C:τ_1
                ((λ C:x_arg C:τ_1
                   (mon C:k C:l C:j C:κ_2
                        (C:x_1 (mon C:l C:k C:j C:κ_1 C:x))))
                 (mon C:l C:j C:j C:κ_1 C:x))))
            ((C:τ_1 -> C:τ_2) -> (C:τ_1 -> C:τ_2))
            E:e_4)
   ----------------------------------------------------------------------- "C-Mon-Dep"
   (compile C:Γ
            (mon C:k C:l C:j (C:κ_1 ->i C:x_arg C:κ_2) C:e)
            (C:τ_1 -> C:τ_2)
            ;; remember to evaluate the contract expression first
            (E:e_4 E:e_compiled))]

  [(where C:x ,(variable-not-in (term (C:Γ C:e)) 'x))
   (compile C:Γ C:e (t C:τ_1 C:τ_2) E:e_3)
   (where C:Γ_0 (extend C:Γ C:x (t C:τ_1 C:τ_2)))
   (compile C:Γ_0 (mon C:k C:l C:j C:κ_1 (injl C:x)) C:τ E:e_1)
   (compile C:Γ_0 (mon C:k C:l C:j C:κ_2 (injr C:x)) C:τ E:e_2)
   ------------------------------------------------------------------ "C-Mon-Tuple"
   (compile C:Γ
            (mon C:k C:l C:j (t C:κ_1 C:κ_2) C:e)
            (t C:τ_1 C:τ_2)
            ((λ C:x (t C:τ_1 C:τ_2) (t E:e_1 E:e_2)) E:e_3))]

  ;; Hijack: run the compiled body under a custom handler for 𝒞. It sits
  ;; inside the top-level `wrap`, so it is the nearest handler and catches
  ;; every 𝒞 performed in the dynamic extent of the body.
  [(compile C:Γ C:e C:τ E:e)
   ------------------------------------------------------------- "C-Hijack"
   (compile C:Γ (hijack C:e) C:τ
            ((handler genericeff h-hijack) (λ genericeff unused unit E:e)))]
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
(define-term mteff ())
(define-term genericeff ( con )) ;; add to all expression

(define-term h-check
  ((effcheck
     (Λ α (λ genericeff x α (λ genericeff k α
       (if ((w bool) (λ genericeff _ unit ((injl x) (injr x))))
           (k (injr x))
           (error 99991))))))))

;; The hijacking handler: skip the predicate entirely and resume with the
;; monitored value. Does not re-perform 𝒞, so outer handlers never see it.
(define-term h-hijack
  ((effcheck
     (Λ α (λ genericeff x α (λ genericeff k α
       (k (injr x))))))))

(define-term wrap
  (μ w unit (Λ α (λ genericeff f unit ((handler genericeff h-check) f)))))

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

;; Semantic check: run the source program with ->contracts and the compiled
;; program with ->effects, and compare the observable outcomes.
;;   - blame in source  <=> error in target
;;   - first-order values (num, bool, unit, tuples of them) must be equal
;;   - higher-order values are only required to be values on both sides
(define (observe result)
  (define (contains? pred t)
    (or (pred t) (and (list? t) (ormap (λ (x) (contains? pred x)) t))))
  (define (first-order? v)
    (match v
      [(? number?) #t]
      ['true #t] ['false #t] ['unit #t]
      [`(t ,a ,b) (and (first-order? a) (first-order? b))]
      [_ #f]))
  (match result
    [(list (list e _))
     (cond
       [(contains? (λ (t) (match t [`(blame ,_ ,_) #t] [`(error ,_) #t] [_ #f])) e)
        'blame]
       [(first-order? e) e]
       [else 'procedure])]
    [_ (list 'unexpected result)]))

(define (compile-check-semantics p)
  (define source (apply-reduction-relation* ->contracts-hijack (term (,p ()))))
  (define target (compile-and-run p))
  (test-equal (observe target) (observe source))
  (observe source))


(module+ test
  (define-term pass (flat (λ x num true)))
  (define-term fail (flat (λ x num false)))

  ;; compile-time shape: hijack becomes a handler around the compiled mon
  (compile-expect (hijack (mon k l j fail 1))
                  ((handler genericeff h-hijack)
                   (λ genericeff unused unit
                     ((perform genericeff 𝒞 num) (t (λ x num false) 1)))))

  ;; run the compiled program, compare against an expected observation
  (define-syntax-rule (check-target p expected)
    (test-equal (observe (compile-and-run (term p))) (term expected)))
  (define-syntax-rule (check-source p expected)
    (test-equal (observe (apply-reduction-relation* ->contracts-hijack (term (p ()))))
                (term expected)))

  ;; sanity: without hijack, compiler3 behaves like compiler
  (check-target (add (mon k l j pass 1) (mon k l j pass 2)) 3)
  (check-target (add (mon k l j fail 1) (mon k l j pass 2)) blame)

  ;; two mons, one hijacked: the hijacked failing check is silenced
  (check-source (add (hijack (mon k l j fail 1)) (mon k l j pass 2)) blame)
  (check-target (add (hijack (mon k l j fail 1)) (mon k l j pass 2)) 3)

  ;; the non-hijacked mon is still enforced by the outer handler
  (check-target (add (hijack (mon k l j pass 1)) (mon k l j fail 2)) blame)
  (check-target (add (hijack (mon k l j fail 1)) (mon k l j fail 2)) blame)

  ;; hijack covers every check in its dynamic extent
  (check-target (hijack (add (mon k l j fail 1) (mon k l j fail 2))) 3)
  (check-target (hijack (mon k l j (t fail fail) (t 1 2))) (t 1 2))

  ;; function contracts: checks happen when the guarded function is applied.
  ;; Application inside hijack -> silenced
  (check-target (hijack ((mon k l j (pass -> fail) (λ x num (add x 1))) 10)) 11)
  ;; Hijack only around creating the wrapper -> the checks run later, outside
  ;; the handler, so they escape to the default handler and blame.
  (check-target ((hijack (mon k l j (pass -> fail) (λ x num (add x 1)))) 10) blame)

  ;; dependent contracts behave the same way
  (check-target (hijack ((mon k l j
                              (pass ->i y (flat (λ x num (zero? (sub x y)))))
                              (λ x num (add x 1)))
                         10))
                11)
)
