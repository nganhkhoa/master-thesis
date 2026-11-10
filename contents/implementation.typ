#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/codly:2.0.0" as codly
#import "@preview/codly-languages:0.1.1": *

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, proof
#import "/utils.typ": load-bib, no-ref

#show raw.where(block: true): codly.new
#show: codly.theme("github-light", block: (text: (size: 7pt)))

#show: no-ref

= Implementation

Our formal models are implemented in Redex and in OCaml. While the Redex models are closer to the formal compiler models, the OCaml implementation is more practical.

== Redex models

We model three languages: #langb, #langc, #lange, and two compilers one for local, and non-local. To model the compiler, we create a Redex union language of #langc and #lange, and define a judgement `(compile C:Γ C:x C:τ E:x)` where `C:` belongs to #langc and `E:` belongs to #lange, and the input output model is `(compile I I O O)`. The interesting compilation rules are displayed in @redex-compiler-non-local. @redex-compiler-local shows the local version compiler where all rules are kept except for the flat compilation rule accompanied by a handler.

For non-local compiler, their wrappers must be created accordingly to @redex-shallow-compiler-wrapper (using shallow handlers) or to @redex-deep-compiler-wrapper (using deep handlers). We use `genericeff` as a common effect list consisting of the single contract checking effect identifier for type checking.

#figure(caption: "Non-local compiler")[
```racket
[(compile C:Γ C:e_1 (C:τ -> bool) E:e_1)
 (compile C:Γ C:e_2 C:τ E:e_2)
 ------------------------------------------------------- "C-Mon-Flat"
 (compile C:Γ (mon C:k C:l C:j (flat C:e_1) C:e_2) C:τ
          ((perform genericeff 𝒞 C:τ) (t E:e_1 E:e_2)))]

[(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled)
 (where (C:x C:x_1) ,(variables-not-in (term (C:Γ C:e)) '(x x_1)))
 (compile C:Γ
          (λ C:x_1 (C:τ_1 -> C:τ_2) (λ C:x C:τ_1
              (mon C:k C:l C:j C:κ_2 (C:x_1 (mon C:l C:k C:j C:κ_1 C:x)))))
          ((C:τ_1 -> C:τ_2) -> (C:τ_1 -> C:τ_2))
          E:e_4)
 -------------------------------------------------------------------------- "C-Mon-Func"
 (compile C:Γ
          (mon C:k C:l C:j (C:κ_1 -> C:κ_2) C:e)
          (C:τ_1 -> C:τ_2)
          (E:e_4 E:e_compiled))]

[(compile C:Γ C:e (C:τ_1 -> C:τ_2) E:e_compiled)
 (where (C:x C:x_1)
       ,(variables-not-in (term (C:Γ C:e C:κ_1 C:κ_2 C:x_arg)) '(x x_1)))
 (compile C:Γ
          (λ C:x_1 (C:τ_1 -> C:τ_2) (λ C:x C:τ_1 ((λ C:x_arg C:τ_1
                 (mon C:k C:l C:j C:κ_2
                      (C:x_1 (mon C:l C:k C:j C:κ_1 C:x))))
               (mon C:l C:j C:j C:κ_1 C:x))))
          ((C:τ_1 -> C:τ_2) -> (C:τ_1 -> C:τ_2))
          E:e_4)
 ------------------------------------------------------------------------ "C-Mon-Dep"
 (compile C:Γ
          (mon C:k C:l C:j (C:κ_1 ->i C:x_arg C:κ_2) C:e)
          (C:τ_1 -> C:τ_2)
          (E:e_4 E:e_compiled))]
```
]<redex-compiler-non-local>

#figure(caption: "Local compiler")[
```racket
[(compile C:Γ C:e_1 (C:τ -> bool) E:e_1)
 (compile C:Γ C:e_2 C:τ E:e_2)
 ----------------------------------------------------- "C-Mon-Flat"
 (compile C:Γ (mon C:k C:l C:j (flat C:e_1) C:e_2) C:τ
          ((s-handler (𝒞)
             ((𝒞
               (Λ β (λ (𝒞) x β (λ (𝒞) k β
                 (if ((injl x) (injr x))
                     (k (injr x))
                     (error 99991))))))))
           (λ (𝒞) ignored unit
             ((perform (𝒞) 𝒞 C:τ) (t E:e_1 E:e_2)))))]
```
] <redex-compiler-local>

#figure(caption: "Shallow handler wrapper for non-local compiler")[
```racket
(define-term h-check
  ((effcheck
     (Λ α (λ genericeff x α (λ genericeff k α
       ((w α) (λ genericeff _ unit
         (if ((injl x) (injr x))
             (k (injr x))
             (error 99991))))))))))

(define-term wrap
  (μ w unit (Λ α (λ genericeff f unit ((s-handler genericeff h-check) f)))))
```
] <redex-shallow-compiler-wrapper>


#figure(caption: "Deep handler wrapper for non-local compiler")[
```racket
(define-term h-check
  ((effcheck
     (Λ α (λ genericeff x α (λ genericeff k α
       (if ((w bool) (λ genericeff _ unit ((injl x) (injr x))))
           (k (injr x))
           (error 99991))))))))

(define-term wrap
  (μ w unit (Λ α (λ genericeff f unit ((d-handler genericeff h-check) f)))))
```
] <redex-deep-compiler-wrapper>

== OCaml implementation

We have chosen OCaml as a base language to implement our contract system. The choice was purely because of two things. First, OCaml 5 has support for effect handlers built-in. Second, OCaml has a macro system that we can rely on to modify the program. On top of these two reasons is the author's familiarity with the language.

=== OCaml Attributes and Rewritters

OCaml does not have a clean "macro system". In fact, OCaml compilation chain allows users to introduce a rewritter defined as a source to source transformation. A rewritter can be any program that takes the whole file source, and returns a (modified) file source. Because there is no restriction, rewritters are free to modify, add, delete source code. However, useful rewritters will try to edit programs with intention. For this purpose, ppxlib, a common library is provided for writting rewritters, allowing them to parse and modify source code in Abstract Syntax Tree (AST) objects. OCaml syntax also support rewritters by providing a way to annotate source code places in AST through the use of _attributes_. Attributes are enclosed in square brackets, tagged with an identifier and carry "code-like" payloads. Readers familiar with OCaml might have used attributes already, as one of the most commonly used attributes is `[@@deriving show]` to allow structs to be print-able.

=== OCaml Contracts as Attributes

Using attributes, we define contracts and our rewritter acts as the compiler as defined. Wrappers can be added manually or automatically with an attribute denoting the wrapper placement. The modified source code might use functions, objects that was not defined previously, therefore we expect users to include our library where it contains all extra declarations for compilation and running.

In @ocaml-contract-attributes is the list of some contract attributes syntax. Users attach these attributes to guard a value, function or variable with some contract `c`, which we discuss later on how to write different contract types. To install the wrapper, users only need to attach `%contract_main` to the expression that has contract checking code.

#figure(caption: "Attributes for Contracts", table(
  columns: 2,

  [Attributes], [Meaning],
  [`let[@contract c] x = e`], [Place contract `c` on value/function `x`],
  [`[%contract_main] e`], [Install the contract wrapper on `e`],
  [`let%contract_main f = e`], [Install the contract wrapper on `f`],
  [`[%mon c ~pos:p ~neg:n ~loc:j] e`], [Place contract `c` on `e` with explicit labels],
)) <ocaml-contract-attributes>

Our rewritter supports three main types of contracts, flat, functional, and dependent. Firstly, a flat contract is a function that takes a value and returns boolean. Secondly, since contracts can be nested far inside by the use of functional and dpendent contracts, the structured syntax is recursive: if `c_1,c_2` is a contract, then `c_1 @-> c_2` and `dep c_1 (fun x -> c_2)` are contracts. During the writing of contracts, for brewvity, users can use identifiers to a function (must be already in-scope) instead of writing the contract code in full.

Because OCaml is a curry-by-default language, we take that same approach to introduce contracts for multi-parameters functions. For functional contracts, the syntax is clear and precise. For dependent contract, the syntax creates a nested structure that is unnatural to the human eyes. We provide a different syntax for dependent contracts that is inspired by Racket's contract macro, `[@contract dep_args [(arg_1, c_1); ...] (fun arg_1 arg_2 ... -> e)]`. The new syntax is purely for human users, it will be expanded into the nested structure accordingly during the rewriting process before compiling into contract checking code. Below is the example syntax for functional and dependent contracts annotation.

```ocaml
let [@contract c_1 @-> c_2 @-> c_3]
  f x y = e
let [@contract dep c_1 (fun x -> (dep c_2 (fun y -> c_3)))]
  g x y = e
let [@contract dep_args [(x,c_1); (y,c_2)] (fun x y -> c_3)]
  h x y = e
```

The macro unwraps functional and dependent contracts with lambdas until flat contract and simply convert it to an effect invocation. Accordingly to our formal model, there is only one effect, defined as in @ocaml-check-effect. Labels are automatically added, and during the lambdas unrolling, labels are swapped in the correct manner.

#figure[
```ocaml
type label = string
type _ Effect.t +=
  | Check : { pos : label; loc : label; pred : 'a -> bool; value : 'a } -> 'a Effect.t
```
]<ocaml-check-effect>

=== States encoding contracts

Our OCaml model also implement contract states, which we briefly introduced in @compiler-formal-states. For this to work, we provide attributes to declare contract states, `%%contract_states`; and a wrapper attribute with states initialization, `%contract_main_states`. Declaring contract states are a series of let binding expressions, with their names, types and initial value. For each state declaration, the rewritter automatically generate two new effects, `%contract_get_*` and `%contract_set_*`. When writing the contracts, users can use these attributes to obtain or modify the states. Due to the limitation of OCaml rewritter, these states are only available when the whole program is in a single file if using `%contract_main_states`. Otherwise, users can manually write the wrapper to provide all possible states.

@ocaml-example-contract-states illustrates the simple example where a state is used to record inputs to the same function. Because states are controlled using effects, and the macro system does not decouple contract effects from main program effects, users can call these effects. Technically, our rewritter can try to limit the usage of these `%contract_get_*,%contract_set_*` attributes to contract checking code if we can identify contract checking code. However, since contracts can be an identifier of some function, we find that distinction undesirable.

#figure[
```ocaml
[%%contract_states
  let previous : int option = None]
let nondecreasing input =
  match [%contract_get_previous] with
  | Some previous when input < previous -> false
  | _ ->
      [%contract_set_previous (Some input)];
      true
let[@contract nondecreasing @-> Contract.any] process input = input * 2
let () = [%contract_main_states]
    (List.iter
       (fun input ->
         try Printf.printf "%d -> %d\n" input (process input)
         with Contract.Blame _ -> Printf.printf "%d -> rejected\n" input)
       [ 1; 3; 3; 2; 5 ])
```
] <ocaml-example-contract-states>

=== Boxes and Vectors contracts

Our OCaml implementation provides special types of boxes and vectors that acts similarly to Racket's chaperone#footnote([Opaque proxies around objects with support for contracts]). Our boxes and vectors are encoded as structs with methods. They should not be called directly, but through the provided functions. For example, a box is created using `Box.create`, and its content can be obtained by calling `Box.get`. Through this encoding, we obtain an opaque box/vector with methods as functions. Contracts can now be added directly through these functions. We provide attributes `[@contract box c]` and `[@contract vector c]` that installs the contract `c` to boxes/vectors get/set methods. The rewritter will create a new struct object and install the contracts into the methods. This approach breaks the equality of boxes/vectors but replicates the opaque implementation of chaperone.

=== Mismatch with the formal models

Although OCaml provides a similar model to #lange which we can adapt to add contracts ($mon(k,l,j,kappa,e)$) and compile them away using the rules as defined in @compiler-rules, there is a slight difference between the formal models and the OCaml rewritter. One of the more obvious and important mismatch is dependent contracts input. In the formal models, we build up the new contract $mon(k,l,j,dep(kappa_1,lambda y. kappa_2),e)$ for codomain as $kappa_2[y:=mon(l,j,j,kappa_1,x)]$ where $x$ is created fresh during lambda padding. In our model, if $y$ appears multiple times in $kappa_2$ then the same contract runs that many times. In a language where there is no mutable boxes, such as #lange, running the same code multiple times has no difference from running it once. However, OCaml has mutable boxes, and to be careful, we adjusted the implementation to run the contract once, unless it's a function.
