#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(require "base.rkt")

(define-extended-language Contracts Base
  (κ ::= (flat e) (κ -> κ) (κ ->i x κ) (t κ κ))

  (e ::= ....
         (mon k l j κ e)
         (check k j e v)
         (blame k j))

  (v ::= ....
         (guard k l j κ v))

  (E ::= ....
         (mon k l j κ E)
         (check k j E v))

  (k l j ::= variable-not-otherwise-mentioned)

  #:binding-forms (κ ->i x κ #:refers-to x))

(define ->contracts
  (extend-reduction-relation ->base Contracts
    [==> (check k j true v) v
         CHECK-TRUE]
    [==> (check k j false v) (blame k j)
         CHECK-FALSE]

    [==> (mon k l j (flat e) v)
         (check k j (e v) v)
         MON-FLAT]

    [==> (mon k l j κ v) (guard k l j κ v)
         (side-condition (not (redex-match? Contracts (flat e) (term κ))))
         MON-GUARD]

    [==> ((guard k l j (κ_1 -> κ_2) v_1) v_2)
         (mon k l j κ_2 (v_1 (mon k l j κ_1 v_2)))
         GUARD-FUNC]

    [==> ((guard k l j (κ_1 ->i x κ_2) v_1) v_2)
         (mon k l j (substitute κ_2 x (mon l j j κ_1 v_2)) (v_1 (mon l k j κ_1 v_2)))
         GUARD-DEP]

    [==> (injl (guard k l j (t κ_1 κ_2) (t v_1 v_2)))
         (guard k l j κ_1 v_1)
         GUARD-INJ-LEFT]

    [==> (injl (guard k l j (t κ_1 κ_2) (t v_1 v_2)))
         (guard k l j κ_2 v_2)
         GUARD-INJ-RIGHT]

    with
    [(--> ((in-hole E before) σ) ((in-hole E after) σ))
     (==> before after)]))

(define ->contracts*
  (compatible-closure ->contracts Contracts E))

(module+ test
  (test-match Contracts e (term (blame k j)))

  (test-match Contracts e
    (term (mon k l j
               ((flat (λ x num true)) -> (flat (λ x num false)))
               (λ x num (add x 1)))))

  (test-->> ->contracts*
    (term (((mon k l j
                ((flat (λ x num true)) -> (flat (λ x num false)))
                (λ x num (add x 1)))
           10) ()))
    (term ((blame k j) ())))

  (test-->> ->contracts*
    (term (((mon k l j
                ((flat (λ x num true)) ->i y (flat (λ x num (zero? (sub x y)))))
                (λ x num (add x 1)))
           10) ()))
    (term ((blame k j) ())))
)
