#lang racket

(require "base.rkt")
(require "effects.rkt")
(require "contracts.rkt")
(require "compiler.rkt")

(require redex/pict
         redex/reduction-semantics
         pict
         racket/draw)

;; Takes a Redex artifact and renders it as a PNG.
(define (save-artifact-as-png v filename [scale-factor 2])
  (define artifact-pict
    ;; Parameterize the rendering width to stop forced line breaks.
    ;; Setting columns to 'infinity disables auto-wrapping for wide terms.
    (parameterize ([pretty-print-columns 'infinity]
                   [rule-pict-style 'horizontal])
      (cond
        [(compiled-lang? v)
         (language->pict v)]
        [(reduction-relation? v)
         (render-reduction-relation v #f)]
        [(judgment-form? v)
         (render-judgment-form v #f)]
        [else
         (error 'save-artifact-as-png
                "Unsupported artifact type. Expected language, reduction relation, or judgment form. Got: ~v" v)])))

  (define scaled-pict (scale artifact-pict scale-factor))

  (let ([bmp (pict->bitmap scaled-pict)])
    (send bmp save-file filename 'png)))

(save-artifact-as-png Base "pics/base.png")
(save-artifact-as-png ->base "pics/base-reduction.png" 4)

(save-artifact-as-png Contracts "pics/contracts.png")
(save-artifact-as-png ->contracts "pics/contracts-reduction.png" 4)

(save-artifact-as-png Effects "pics/effects.png")
(save-artifact-as-png ->effects "pics/effects-reduction.png" 4)

(with-atomic-rewriter
 'C:e_1 "e_1"
 (with-atomic-rewriter
  'C:e_2 "e_2"
  (with-atomic-rewriter
   'C:τ "τ"
   (with-atomic-rewriter
    'E:e_1 "e_1"
    (with-atomic-rewriter
     'E:e_2 "e_2"
     (with-atomic-rewriter
      '-> " → "
      (with-atomic-rewriter
       'bool "bool"
       (with-atomic-rewriter
        'perform (lambda () (colorize (text "perform" '(bold . modern) 12) "darkorange"))
        (with-compound-rewriter
         'compile
         (lambda (lws)
           ;; Skip index 0 "(" and index 1 "compile"
           (list ""
                 (list-ref lws 2) " ⊢ "
                 (list-ref lws 3) " : "
                 (list-ref lws 4) " ⇝ "
                 (list-ref lws 5) ""))

         (parameterize ([rule-pict-style 'horizontal])
           (save-artifact-as-png compile "pics/compiler.png")))))))))))
