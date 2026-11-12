#lang racket

;; Compare the actual blamed party in the source and every compiler variant.
;; Source blame can be left in an evaluation context, while target blame aborts.
(require rackunit redex/reduction-semantics
         "contracts.rkt" "effects.rkt"
         (prefix-in deep: "compiler-deep.rkt")
         (prefix-in inner: "compiler-deep-inner.rkt")
         (prefix-in shallow: "compiler-shallow.rkt")
         (prefix-in local: "compiler-local.rkt")
         (prefix-in local-deep: "compiler-local-deep.rkt"))

(define (source-blame e)
  (match e
    [`(blame ,party ,_) party]
    [(? list?) (ormap source-blame e)]
    [_ #f]))
(define (source-result p)
  (match (apply-reduction-relation* ->contracts (term (,p ())))
    [(list (list e _)) (match (source-blame e) [#f e] [party `(blame ,party)])]
    [other `(unexpected ,other)]))
(define (target-result result)
  (match result
    [(list (list `(blame (party ,party)) _)) `(blame ,(string->symbol party))]
    [(list (list e _)) e]
    [other `(unexpected ,other)]))
(define (local-run p)
  (define compiled (term (local:run-compiler ,p)))
  (apply-reduction-relation* ->effects (term (,compiled ()))))

(module+ test
  (define runners
    (list (cons 'deep deep:compile-and-run)
          (cons 'deep-inner inner:compile-and-run)
          (cons 'shallow shallow:compile-and-run)
          (cons 'local local-run)
          (cons 'local-deep local-deep:compile-and-run/local-deep)))
  (define cases
    (list
     (list 'flat (term (mon provider client site (flat (λ x num false)) 7))
           '(blame provider))
     (list 'function-domain
           (term ((mon provider client site
                       ((flat (λ x num false)) -> (flat (λ x num true)))
                       (λ x num x)) 7)) '(blame client))
     (list 'function-range
           (term ((mon provider client site
                       ((flat (λ x num true)) -> (flat (λ x num false)))
                       (λ x num x)) 7)) '(blame provider))
     (list 'dependent-domain
           (term ((mon provider client site
                       ((flat (λ x num false)) ->i y (flat (λ x num true)))
                       (λ x num x)) 7)) '(blame client))
     (list 'dependent-range
           (term ((mon provider client site
                       ((flat (λ x num true)) ->i y (flat (λ x num false)))
                       (λ x num x)) 7)) '(blame provider))
     ;; Both the dependent monitor and the ordinary function monitor flip
     ;; labels, so two domain crossings restore the provider label.
     (list 'nested-domain
           (term ((mon provider client site
                       (((flat (λ x num false)) -> (flat (λ x num true)))
                        ->i f (flat (λ r num true)))
                       (λ f (num -> num) (f 7)))
                  (λ x num x))) '(blame provider))
     ;; The dependent range substitutes a separate (client, site, site)
     ;; monitor. Its dependent function domain must therefore blame site.
     (list 'dependent-substitution-site
           (term ((mon provider client site
                       (((flat (λ x num false)) ->i z (flat (λ x num true)))
                        ->i f (flat (λ r num (zero? (f 1)))))
                       (λ f (num -> num) 0))
                  (λ x num x))) '(blame site))
     (list 'success
           (term ((mon provider client site
                       ((flat (λ x num true)) -> (flat (λ x num true)))
                       (λ x num x)) 7)) 7)))
  (for ([case (in-list cases)])
    (match-define (list name p expected) case)
    (check-equal? (source-result p) expected (format "source ~a" name))
    (for ([runner (in-list runners)])
      (check-equal? (target-result ((cdr runner) p)) expected
                    (format "~a ~a" (car runner) name)))))
