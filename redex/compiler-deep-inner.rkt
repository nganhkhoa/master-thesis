#lang racket

;; Non-local deep-handler variation.  The compiler and its operation payloads
;; are unchanged; only the recursive wrapper's operation clause differs.
(require redex/reduction-semantics
         "effects.rkt"
         (except-in "compiler-deep.rkt" wrap compile-and-run))

(provide CompilerLang compile run-compiler run-type translate-type
         wrap compile-and-run)

;; Unlike compiler-deep's (if (wrap predicate) (k value) blame), run the
;; *whole* conditional under the recursive wrapper.  A resumed deep
;; continuation also reinstalls its own handler, so nested checks may traverse
;; a different stack of handlers even when the observable outcome is the same.
(define-term h-check-inner
  ((𝒞
    (Λ α (λ () x (t party (t (α -> (con) bool) α))
      (λ () k (α -> () β)
        ((w β)
         (λ (con) ignored unit
           (if ((injl (injr x)) (injr (injr x)))
               (k (injr (injr x)))
               (blame (injl x)))))))))))

(define-term wrap
  (μ w (∀ β ((unit -> (con) β) -> () β))
    (Λ β (λ () f (unit -> (con) β) ((d-handler () h-check-inner) f)))))

(define (compile-and-run p)
  (apply-reduction-relation*
   ->effects
   (term (((wrap (translate-type (run-type ,p)))
           (λ (con) _ unit (run-compiler ,p))) ()))))

(module* trace-support #f
  (provide nested-pass nested-fail trace)
  (define nested-pass
    (term (((mon provider client site
                 ((flat (λ x num true)) ->i y
                  ((flat (λ z num true)) ->i w
                   (flat (λ r num (eq r (add y w))))))
                 (λ a num (λ b num (add a b)))) 2) 3)))
  (define nested-fail
    (term (((mon provider client site
                 ((flat (λ x num true)) ->i y
                  ((flat (λ z num true)) ->i w
                   (flat (λ r num (eq r (add y w))))))
                 (λ a num (λ b num (sub a b)))) 2) 3)))

  ;; Reproducible, non-GUI trace with rule names; fail on nondeterminism or a
  ;; runaway trace instead of silently choosing a branch. Invoke with --trace.
  (define (trace relation initial)
    (let loop ([state initial] [n 0] [rules '()])
      (when (> n 1000) (error 'trace "step limit exceeded"))
      (define next (apply-reduction-relation/tag-with-names relation state))
      (cond [(null? next) (values n (reverse rules) state)]
            [(null? (cdr next))
             (loop (cadar next) (add1 n) (cons (caar next) rules))]
            [else (error 'trace "nondeterministic state: ~s" state)])))
)

(module+ test
  (require rackunit "contracts.rkt"
           (submod ".." trace-support)
           (prefix-in original: "compiler-deep.rkt"))

  ;; Source blame can remain inside an evaluation context; target blame aborts
  ;; to the top. Compare its positive party, not its different representation.
  (define (source-blame t)
    (match t
      [`(blame ,k ,_) k]
      [(? list?) (ormap source-blame t)]
      [_ #f]))
  (define (source-observation p)
    (match (apply-reduction-relation* ->contracts (term (,p ())))
      [(list (list e _)) (cond [(source-blame e) => (λ (k) `(blame ,k))]
                               [else e])]
      [other `(unexpected ,other)]))
  (define (target-observation p [run compile-and-run])
    (match (run p)
      [(list (list `(blame (party ,p)) _)) `(blame ,(string->symbol p))]
      [(list (list e _)) e]
      [other `(unexpected ,other)]))

  (define cases
    (list
     (list (term 7) 7)
     (list (term (mon provider client site (flat (λ x num true)) 7)) 7)
     (list (term (mon provider client site (flat (λ x num false)) 7)) '(blame provider))
     (list (term (add (mon p q s (flat (λ x num true)) 2)
                      (mon p q s (flat (λ x num true)) 3))) 5)
     (list (term (mon p q s (t (flat (λ x num true)) (flat (λ b bool true)))
                      (t 2 true))) '(t 2 true))
          (list (term ((mon provider client site
                       ((flat (λ x num true)) -> (flat (λ r num false)))
                       (λ x num x)) 3)) '(blame provider))
     ;; Dependent GUARD-DEP flips k/l for the function argument.
     (list (term ((mon provider client site
                       ((flat (λ x num false)) ->i y (flat (λ r num true)))
                       (λ x num x)) 3)) '(blame client))
     (list nested-pass 5)
     (list nested-fail '(blame provider))
     ;; A monitor inside the predicate requires a recursive handler.
     (list (term (mon outer peer site
                      (flat (λ x num (mon inner peer site (flat (λ b bool true)) true)))
                      9)) 9)
     (list (term (mon outer peer site
                      (flat (λ x num (mon inner peer site (flat (λ b bool false)) true)))
                      9)) '(blame inner))))
  (define Σ-check
    (term ((con : (𝒞 -> (∀ α ((t party (t (α -> (con) bool) α)) -> () α)))))))
  (check-true (judgment-holds (⊢ ,Σ-check () wrap
                               (∀ β ((unit -> (con) β) -> () β)) ())))
  (for ([case (in-list cases)])
    (match-define (list p expected) case)
    (check-equal? (source-observation p) expected (format "source ~s" p))
    (check-equal? (target-observation p) expected (format "target ~s" p))
    (check-equal? (target-observation p original:compile-and-run) expected
                  (format "original ~s" p))
    (define compiled (term (run-compiler ,p)))
    (check-not-false (pair? (judgment-holds (⊢ ,Σ-check () ,compiled τ (con)) τ))
                     (format "target type ~s" p)))
  ;; Non-dependent domains swap parties under GUARD-FUNC.
  (define domain-fail
    (term ((mon provider client site
                ((flat (λ x num false)) -> (flat (λ r num true)))
                (λ x num x)) 3)))
  (check-equal? (source-observation domain-fail) '(blame client))
  (check-equal? (target-observation domain-fail) '(blame client))
  (check-equal? (target-observation domain-fail original:compile-and-run) '(blame client)))

(module+ main
  (require (submod ".." trace-support) "contracts.rkt"
           (prefix-in original: "compiler-deep.rkt"))
  (unless (equal? (vector->list (current-command-line-arguments)) '("--trace"))
    (error 'main "use --trace"))
  (for ([p (list nested-pass nested-fail)] [label '(pass fail)])
    (printf "~a\n" label)
    (for ([kind '(source original inner)])
      (define initial
        (case kind
          [(source) (term (,p ()))]
          [(original) (term (((original:wrap (original:translate-type (original:run-type ,p)))
                              (λ (con) _ unit (original:run-compiler ,p))) ()))]
          [(inner) (term (((wrap (translate-type (run-type ,p)))
                           (λ (con) _ unit (run-compiler ,p))) ()))]))
      (define-values (n rules last)
        (trace (if (eq? kind 'source) ->contracts ->effects) initial))
      (printf "  ~a: ~a steps; rules ~s\n  final: ~s\n" kind n rules last))))
