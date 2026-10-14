#lang racket

;; Erasure of the *surface* contract language.  Unlike compiler.rkt, this
;; compiler has no run-time representation for contracts: a monitor is simply
;; replaced by the expression that it protects.

(provide (all-defined-out))

(require redex/reduction-semantics
         "base.rkt"
         "contracts.rkt")

;; `erase` is intentionally defined only for source expressions (in
;; particular, before `mon` has reduced to `check` or `guard`).  Its results
;; use only the constructors inherited from Base, even though its codomain is
;; written as `e` so that Redex can conveniently recurse over Contracts.
(define-metafunction Contracts
  erase : e -> e

  ;; Base values and expressions.
  [(erase n) n]
  [(erase b) b]
  [(erase unit) unit]
  [(erase x) x]
  [(erase loc) loc]
  [(erase (λ x τ e))
   (λ x τ (erase e))]
  [(erase (μ x τ e))
   (μ x τ (erase e))]
  [(erase (t e_1 e_2))
   (t (erase e_1) (erase e_2))]
  [(erase (e_1 e_2))
   ((erase e_1) (erase e_2))]
  [(erase (injl e))
   (injl (erase e))]
  [(erase (injr e))
   (injr (erase e))]
  [(erase (o e ...))
   (o (erase e) ...)]
  [(erase (if e_1 e_2 e_3))
   (if (erase e_1) (erase e_2) (erase e_3))]
  [(erase (new e))
   (new (erase e))]
  [(erase (get e))
   (get (erase e))]
  [(erase (set e_1 e_2))
   (set (erase e_1) (erase e_2))]

  ;; Contracts are compile-time-only.  Crucially, this rule recursively erases
  ;; the protected expression, so nested monitors do not survive either.
  [(erase (mon k l j κ e))
   (erase e)])

;; A descriptive entry point for clients that refer to the transformation as
;; a compiler rather than as the erasure function itself.
(define-metafunction Contracts
  run-erasure : e -> e
  [(run-erasure e) (erase e)])

(module+ test
  (require rackunit)

  ;; Flat monitors disappear, including monitors below ordinary expressions.
  (check-equal?
   (term (erase (add (mon pos neg loc (flat (λ x num true)) 1) 2)))
   (term (add 1 2)))

  ;; A function remains a function; monitors in its body and around the
  ;; function are erased recursively.
  (check-true
   (alpha-equivalent? Contracts
                      (term (erase
                             (mon pos neg loc
                                  ((flat (λ x num true)) -> (flat (λ x num true)))
                                  (λ x num (mon pos neg loc (flat (λ y num true)) x)))))
                      (term (λ x num x))))

  ;; The output of erasure is a Base expression, not contract syntax.
  (check-true
   (redex-match? Base e
                 (term (run-erasure
                        (mon pos neg loc (flat (λ x num true))
                             (t 1 2))))))

  ;; Executable instances of the boolean erasure theorem.  Each check asserts
  ;; both halves independently: the monitored source reduces to `answer`, and
  ;; its erased Base program reduces to precisely that same boolean.
  (define (boolean-result relation configuration)
    (for/first ([result (in-list (apply-reduction-relation* relation configuration))]
                #:when (match result
                         [`(,boolean ,_store) (memq boolean '(true false))]
                         [_ #f]))
      (match result [`(,boolean ,_store) boolean])))

  (define-syntax-rule (check-boolean-erasure source answer)
    (let ([source-result
           (boolean-result ->contracts* (term (source ()) ))]
          [erased-result
           (boolean-result ->base (term ((erase source) ())))])
      ;; Equality is the theorem assertion; the expected result documents the
      ;; terminating source instance being exercised.
      (check-equal? source-result (term answer))
      (check-equal? erased-result (term answer))
      (check-equal? erased-result source-result)))

  ;; 1--4: direct flat checks, nesting, and checks in ordinary evaluation
  ;; contexts.
  (check-boolean-erasure
   (zero? (mon k l j (flat (λ x num true)) 7)) false)
  (check-boolean-erasure
   (mon k l j (flat (λ x bool true)) false) false)
  (check-boolean-erasure
   (zero? (mon k l j (flat (λ x num true))
               (mon k2 l2 j2 (flat (λ x num true)) 9)))
   false)
  (check-boolean-erasure
   (zero? (mon k l j (flat (λ x num true)) 0)) true)

  ;; 5--7: monitors occur in conditionals, branches, and function bodies.
  (check-boolean-erasure
   (if (mon k l j (flat (λ x bool true)) true) false true)
   false)
  (check-boolean-erasure
   (if false
       (mon k l j (flat (λ x num true)) 0)
       (zero? (mon k2 l2 j2 (flat (λ x num true)) 0)))
   true)
  (check-boolean-erasure
   ((λ x num (zero? (mon k l j (flat (λ y num true)) x))) 0)
   true)

  ;; 8--11: higher-order contracts, including an escaping protected function
  ;; and an indy/dependent function contract.
  (check-boolean-erasure
   (zero?
    ((mon k l j
          ((flat (λ x num true)) -> (flat (λ y num true)))
          (λ x num x))
     0))
   true)
  (check-boolean-erasure
   (zero?
    ((mon k l j
          ((flat (λ x num true)) -> (flat (λ y num true)))
          (λ x num x))
     0))
   true)
  (check-boolean-erasure
   (zero?
    ((mon k l j
          ((flat (λ x num true)) -> (flat (λ y num true)))
          (λ x num 1))
     0))
   false)
  (check-boolean-erasure
   (zero?
    ((mon k l j
          ((flat (λ x num true)) ->i y (flat (λ z num true)))
          (λ x num x))
     0))
   true)

  ;; 12--14: tuple contracts produce monitored components, which are then
  ;; consumed through projections and can themselves be functions.
  (check-boolean-erasure
   (zero? (injl (mon k l j
                      (t (flat (λ x num true))
                         (flat (λ y num true)))
                      (t 0 1))))
   true)
  (check-boolean-erasure
   (zero? (injr (mon k l j
                      (t (flat (λ x num true))
                         (flat (λ y num true)))
                      (t 0 1))))
   false)
  (check-boolean-erasure
   (zero? ((injl (mon k l j
                       (t ((flat (λ x num true)) ->
                           (flat (λ y num true)))
                          (flat (λ z num true)))
                       (t (λ x num x) 5)))
            0))
   true)

  ;; 15--16: evaluation beneath monitors also works with state and recursion.
  (check-boolean-erasure
   (zero? (mon k l j (flat (λ x num true)) (get (new 0))))
   true)
  (check-boolean-erasure
   ((μ loop (num -> bool)
       (λ x num
         (if (zero? x)
             true
             (loop (sub x 1)))))
    (mon k l j (flat (λ x num true)) 3))
   true))
