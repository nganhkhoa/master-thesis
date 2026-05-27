#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(require "base.rkt")

(define-extended-language Effects Base
  (K ::= * (K -> K) eff lab blab)

  (ε ::= (lab ...))

  (τ ::= ....
         unit
         α
         (τ -> ε τ)
         (∀ α τ))

  (h ::= ((op f) ...))
  (f ::= (Λ α (λ x τ_1 (λ k τ_2 e))))

  (e ::= ....
         (e τ)
         (handle h e)
         (blame e))

  (v ::= ....
         unit
         (Λ α v)
         (handler h)
         (perform op τ))

  (E ::= ....
         (E τ)
         (handle h E)
         (blame E))

  ;; special kontinuation variable
  (k variable-not-otherwise-mentioned)
  ;; type variable for polymorphism
  (α variable-not-otherwise-mentioned)
  ;; abitrary op name
  (op variable-not-otherwise-mentioned)

  #:binding-forms (Λ α v #:refers-to α))

(define-metafunction Effects
  in-handler : op h -> boolean
  [(in-handler op_1
               ((op_1 f_1) (op_2 f_2) ... ))
               #true]
  [(in-handler op_1
               ((op_2 f_2) (op_3 f_3) ... ))
               (in-handler op_1 ((op_3 f_3) ...))]
  [(in-handler _ _) #false])

(define-metafunction Effects
  find-op-in-handler : op h -> (τ f)
  [(find-op-in-handler
     op
     ((op_1 f_1) ... (op (Λ α (λ x τ_1 (λ k τ_2 e)))) (op_2 f_2) ...))
   (τ_2 (Λ α (λ x τ_1 (λ k τ_2 e))))])

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
  [(bop (+ E e)) (bop E)]
  [(bop (+ v E)) (bop E)]
  [(bop (- E e)) (bop E)]
  [(bop (- v E)) (bop E)]
  [(bop (if E e_1 e_2)) (bop E)]
  [(bop (zero? E)) (bop E)]

  ;; not sure about this lol
  [(bop (E τ)) (bop E)]

  [(bop (handle ((op f) ...) E))
   (append-ops (op ...) (bop E))]

  [(bop (handle () E)) (bop E)]
  )

(define-metafunction Effects
  not-in : op (op ...) -> boolean
  [(not-in op (op op_1 ...)) #false]
  [(not-in op (op_1 op_2 ...)) (not-in op (op_2 ...))]
  [(not-in op ()) #true])

(define-metafunction Effects
  unhandled : op E -> boolean
  [(unhandled op E) (not-in op (bop E))])

(define ->effects
  (extend-reduction-relation ->base Effects
    [--> ((Λ α v) τ)
         (substitute v α τ)
         S-TApp]

    [--> ((handler h) v)
         (handle h (v unit))
         HANDLER-VALUE]

    [--> (handle h v)
         v
         HANDLE-VALUE]

    [--> (handle h (in-hole E ((perform op τ) v)))
         (((f τ) v) e)

         (side-condition (term (unhandled op E)))
         (side-condition (term (in-handler op h)))
         (where (τ_2 f) (find-op-in-handler op h))
         (where e (λ y (substitute τ_2 α τ) (handle h (in-hole E y))))
         HANDLE-OP]
  ))

(define ->effects*
  (compatible-closure ->effects Effects E))

(module+ test
  (define-term h-dup ((dup (Λ α (λ x α (λ k α (k (+ x x))))))))
  (define-term h-get ((get (Λ α (λ x α (λ k α (λ s num ((k s) s))))))))
  (define-term h-set ((set (Λ α (λ x α (λ k α (λ s num ((k x) s))))))))

  (define-term h-dummy ((dummy (Λ α (λ x α (λ k α (k x)))))))

  (test-match Effects
    h
    (term h-dup))

  (test-match Effects
    (handle h E)
    (term (handle h-dup (+ hole 1))))

  (test-match Effects
    (handle h (in-hole (+ hole 1) ((perform op τ) v)))
    (term (handle h-dup (+ ((perform op τ) v) 1))))

  ;; make sure that dummy doesn't get called
  (test-->> ->effects*
            (term (handle h-dup (handle h-dummy (+ ((perform dup num) 2) 1))))
            (term 5))


  (define-term h-check
    ((Check (Λ α (λ x α (λ k α (if ((injl (injr x)) (injr (injr x)))
                                   (k (injr (injr x)))
                                   (blame 111))))))))

  (test-match Effects h (term h-check))
  (test-->> ->effects*
          (term (handle h-check ((perform Check α) (t 123 (t (λ x num false) 1)))))
          (term (blame 111)))

  (test-->> ->effects*
          (term (handle h-check ((perform Check α) (t 123 (t (λ x num true) 1)))))
          (term 1))
)
