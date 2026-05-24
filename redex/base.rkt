#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(define-language Base
  (e ::= v (μ x τ e)
         (t e e) (e e)
         (injl e) (injr e)
         (+ e e) (- e e)
         (if e e e) (zero? e))

  (v ::= n b x (λ x τ e) (t v v))

  (E ::= hole
         (E e) (v E)
         (t E e) (t v E)
         (injl E) (injr E)
         (+ E e) (+ v E) (- E e) (- v E)
         (if E e e) (zero? E))

  (τ ::= bool num (τ -> τ) (t τ τ))

  (n ::= integer)
  (b ::= true false)
  (x y z := variable-not-otherwise-mentioned)

  #:binding-forms
  (λ x τ e #:refers-to x))

(define ->base
  (reduction-relation Base
    [--> ((λ x τ e) v)
         (substitute e x v)
         "S-App"]

    [--> (μ x τ e)
         (substitute e x (μ x τ e))
         "S-Fix"]

    [--> (injl (t v_1 v_2)) v_1
         "S-Inj-Left"]

    [--> (injr (t v_1 v_2)) v_2
         "S-Inr-Right"]

    [--> (if true e_1 e_2) e_1
         "S-If-True"]

    [--> (if false e_1 e_2) e_2
         "S-If-False"]

    [--> (+ n_1 n_2)
         ,(+ (term n_1) (term n_2))
         "plus"]

    [--> (- n_1 n_2)
         ,(- (term n_1) (term n_2))
         "minus"]

    [--> (zero? 0) true
         "zero?-t"]

    [--> (zero? n_1) false
         "zero?-f"]))

(define ->base*
  (compatible-closure ->base Base E))

(module+ test
  (test-->> ->base*
            (term (injl (t (+ 1 2) (+ 2 3))))
            (term 3))
)
