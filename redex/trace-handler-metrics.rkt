#lang racket

;; Reproduce with: racket redex/trace-handler-metrics.rkt
;; No traces are written or retained: only current state and maxima are kept.
;; A syntactic occurrence is a list headed by the indicated constructor,
;; anywhere in the entire configuration (expression AND store), including
;; lambda/type-lambda/recursive bodies, handler clauses and continuations.
;; Frames in suspended continuations therefore count as syntactic, not active.
;; The additional no-function-bodies counts traverse the same entire state but
;; omit the body (last field) of each Base/Effects λ and Λ form; their other
;; fields are still traversed. They do not omit μ bodies: μ unfolds as an
;; expression, not a function value. The counts still include non-function
;; branches, handler clauses outside function bodies, and store contents; they
;; are not a reachability, liveness, allocation, or active-stack measure.
;; Active depth is the maximum number of dynamic handle constructors on the
;; path to the hole among all decompositions (in-hole E any) allowed by the
;; actual Effects evaluation-context grammar. Handler clauses and suspended
;; lambdas are not on that path. This also counts a frame ready to return.
;; All maxima include the initial and final configurations, with step 0 initial.
;; These are syntactic tree counts, not allocation counts, heap sizes or costs.

(require redex/reduction-semantics racket/match
         "effects.rkt"
         (prefix-in shallow: "compiler-shallow.rkt")
         (prefix-in deep: "compiler-deep.rkt")
         (prefix-in inner: "compiler-deep-inner.rkt")
         (prefix-in local: "compiler-local.rkt")
         (prefix-in local-deep: "compiler-local-deep.rkt"))

(define addition
  (term (((mon provider client site
               ((flat (λ x num true)) ->i y
                ((flat (λ z num true)) ->i w
                 (flat (λ r num (eq r (add y w))))))
               (λ a num (λ b num (add a b)))) 2) 3)))
(define subtraction
  (term (((mon provider client site
               ((flat (λ x num true)) ->i y
                ((flat (λ z num true)) ->i w
                 (flat (λ r num (eq r (add y w))))))
               (λ a num (λ b num (sub a b)))) 2) 3)))

;; Match the existing runners, including the shallow runner's unit type and
;; (con) thunk annotation. Deep runners infer the target result type.
(define (initial strategy p)
  (case strategy
    [(local-deep) (term ((local-deep:run-compiler ,p) ()))]
    [(local-shallow) (term ((local:run-compiler ,p) ()))]
    [(nonlocal-shallow)
     (term (((shallow:wrap unit)
             (λ (con) _ unit (shallow:run-compiler ,p))) ()))]
    [(deep)
     (term (((deep:wrap (deep:translate-type (deep:run-type ,p)))
             (λ (con) _ unit (deep:run-compiler ,p))) ()))]
    [(deep-inner)
     (term (((inner:wrap (inner:translate-type (inner:run-type ,p)))
             (λ (con) _ unit (inner:run-compiler ,p))) ()))]))

(define (count-headed tree symbols #:omit-function-bodies? [omit? #f])
  ;; Traverse list elements, not successive cdr suffixes as separate nodes.
  ;; Both Base (λ x τ e) and Effects (λ ε x τ e) occur in the language.
  (define (walk t)
    (cond [(pair? t)
           (define function-form?
             (and omit? (list? t)
                  (or (and (eq? (car t) 'λ) (member (length t) '(4 5)))
                      (and (eq? (car t) 'Λ) (= (length t) 3)))))
           (+ (if (memq (car t) symbols) 1 0)
              (walk-elements (if function-form? (drop-right t 1) t)))]
          [else 0]))
  (define (walk-elements xs)
    (cond [(pair? xs) (+ (walk (car xs)) (walk-elements (cdr xs)))]
          [(null? xs) 0]
          [else (walk xs)]))
  (walk tree))

;; There is exactly one hole in each returned E. Do not descend into a
;; handler's clause to measure the evaluation-path depth.
(define hole
  (bind-exp (findf (λ (b) (eq? (bind-name b) 'E))
                   (match-bindings
                    (first (redex-match Effects (in-hole E any) 1))))))
(define (contains-hole? t)
  (or (equal? t hole)
      (and (pair? t) (or (contains-hole? (car t))
                         (contains-hole? (cdr t))))))
(define (context-depth c)
  (cond [(equal? c hole) 0]
        [(and (list? c) (= (length c) 4)
              (memq (car c) '(s-handle d-handle))
              (contains-hole? (fourth c)))
         (add1 (context-depth (fourth c)))]
        [(pair? c)
         (cond [(contains-hole? (car c)) (context-depth (car c))]
               [(contains-hole? (cdr c)) (context-depth (cdr c))]
               [else (error 'context-depth "no hole: ~s" c)])]
        [else (error 'context-depth "no hole: ~s" c)]))
(define (active-depth expression)
  (define decompositions (redex-match Effects (in-hole E any) expression))
  (unless decompositions (error 'active-depth "not an Effects expression: ~s" expression))
  (apply max
         (for/list ([m (in-list decompositions)])
           (define b (findf (λ (b) (eq? (bind-name b) 'E)) (match-bindings m)))
           (context-depth (bind-exp b)))))

;; Each maximum records its earliest state index; maxima need not coincide.
(struct peak (value step) #:transparent)
(define (update p v step)
  (if (> v (peak-value p)) (peak v step) p))
(define (measure strategy p expected)
  (let loop ([state (initial strategy p)] [step 0]
             [values-peak (peak -1 0)] [frames-peak (peak -1 0)]
             [outside-values-peak (peak -1 0)] [outside-frames-peak (peak -1 0)]
             [active-peak (peak -1 0)] [ops 0])
    (when (> step 1000) (error 'measure "step limit exceeded: ~a" strategy))
    (match-define (list expression store) state)
    (define vp (update values-peak (count-headed state '(s-handler d-handler)) step))
    (define fp (update frames-peak (count-headed state '(s-handle d-handle)) step))
    (define ovp (update outside-values-peak
                        (count-headed state '(s-handler d-handler)
                                      #:omit-function-bodies? #t) step))
    (define ofp (update outside-frames-peak
                        (count-headed state '(s-handle d-handle)
                                      #:omit-function-bodies? #t) step))
    (define ap (update active-peak (active-depth expression) step))
    (define next (apply-reduction-relation/tag-with-names ->effects state))
    (cond [(null? next)
           (unless (equal? expression expected)
             (error 'measure "unexpected final state for ~a: ~s" strategy state))
           (printf "~a: steps=~a values=~a@~a frames=~a@~a no-fn-values=~a@~a no-fn-frames=~a@~a active=~a@~a operations=~a final=~s\n"
                   strategy step (peak-value vp) (peak-step vp)
                   (peak-value fp) (peak-step fp)
                   (peak-value ovp) (peak-step ovp) (peak-value ofp) (peak-step ofp)
                   (peak-value ap) (peak-step ap)
                   ops expression)]
          [(null? (cdr next))
           (define rule (caar next))
           (loop (cadar next) (add1 step) vp fp ovp ofp ap
                 (+ ops (if (member rule '("D-HANDLE-OP" "S-HANDLE-OP")) 1 0)))]
          [else (error 'measure "nondeterministic at step ~a: ~s" step state)])))

(module+ main
  (for ([p (list addition subtraction)]
        [label '(addition subtraction)]
        [expected (list 5 '(blame (party "provider")))])
    (printf "~a\n" label)
    (for ([strategy '(local-deep nonlocal-shallow deep deep-inner local-shallow)])
      (measure strategy p expected))))

(module+ test
  (require rackunit)
  ;; Nested dormant handler in a lambda contributes to syntax, not depth.
  (define sample (term (d-handle () ()
                          ((λ () x num (s-handle () () x))
                           (s-handle () () (add 1 2))))))
  (check-equal? (count-headed sample '(s-handle d-handle)) 3)
  (check-equal? (count-headed sample '(s-handle d-handle) #:omit-function-bodies? #t) 2)
  ;; Both lambda syntaxes and type abstraction suppress only their bodies;
  ;; μ does not, and store / non-evaluation branches remain syntactic.
  (define sample-state
    (term ((t (μ x num (d-handler () ()))
              (if true (s-handle () () 1)
                  (λ x num (d-handle () () 2))))
           ((0 (Λ α (d-handler () ())))
            (1 (λ () x num (s-handler () ())))
            (2 (d-handler () ()))))))
  (check-equal? (count-headed sample-state '(s-handler d-handler)) 4)
  (check-equal? (count-headed sample-state '(s-handler d-handler) #:omit-function-bodies? #t) 2)
  (check-equal? (count-headed sample-state '(s-handle d-handle)) 2)
  (check-equal? (count-headed sample-state '(s-handle d-handle) #:omit-function-bodies? #t) 1)
  (check-equal? (count-headed '(x s-handle ()) '(s-handle)) 0)
  (check-equal? (active-depth sample) 2)
  (check-equal? (active-depth (term (λ () x num (d-handle () () x)))) 0)
  (check-equal? (active-depth (term (d-handle () () 1))) 1))
