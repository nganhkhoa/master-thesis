#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/codly:2.0.0" as codly
#import "@preview/codly-languages:0.1.1": *

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, proof, rn
#import "/utils.typ": load-bib, no-ref

#show raw.where(block: true): codly.new
#show: codly.theme("github-light", block: (text: (size: 7pt)))

#show: no-ref

= Implementation <chapter-implementation>

Our formal models are implemented in Redex and in OCaml. While the Redex models are closer to the formal compiler models, the OCaml implementation is more practical.

== Redex models

We model three languages: #langb, #langc, #lange, and two compiler variants, one using in-place handlers and the other using a whole-program handler. To model the compiler, we create a Redex union language of #langc and #lange, and define a judgement

`(compile C:Γ C:x C:τ E:x)`

where `C:` belongs to #langc and `E:` belongs to #lange, and the input output model is `(compile I I O O)`. The interesting compilation rules are displayed in @redex-compiler-non-local. @redex-compiler-local shows the in-place-handler compiler variant where all rules are kept except for the flat compilation rule accompanied by a handler. The whole-program compiler inserts the contract-checking effect $heffcheck$. This is represented in Redex by defining a `genericeff` and used in terms `lambda`, `perform` in the compilation rules. For the #rn("T1") and #rn("T2") translations, wrappers must be applied. The wrappers in Redex for #rn("T1") is in @redex-deep-compiler-wrapper and for #rn("T2") is in @redex-shallow-compiler-wrapper.

#figure(caption: "Compiler for a whole-program handler")[
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

#figure(caption: "Compiler with in-place handlers")[
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
                     (error (injl x)))))))))
           (λ (𝒞) ignored unit
             ((perform (𝒞) 𝒞 C:τ) (t E:e_1 E:e_2)))))]
```
] <redex-compiler-local>


#figure(caption: [Redex #rn("T1") wrapper])[
```racket
(define-term h-check
  ((effcheck
     (Λ α (λ genericeff x α (λ genericeff k α
       (if ((w bool) (λ genericeff _ unit ((injl x) (injr x))))
           (k (injr x))
           (error (injl x)))))))))

(define-term wrap
  (μ w unit (Λ α (λ genericeff f unit ((d-handler genericeff h-check) f)))))
```
] <redex-deep-compiler-wrapper>

#figure(caption: [Redex #rn("T2") wrapper])[
```racket
(define-term effcheck 𝒞)

(define-term h-check
  ((effcheck
     (Λ α (λ () x (t party (t (α -> (con) bool) α))
       (λ () k (α -> (con) β)
         (h (λ (con) _ unit
           (if ((injl (injr x)) (injr (injr x)))
               (k (injr (injr x)))
               (blame (injl x)))))))))))

(define-term H-check
  (μ h ((unit -> (con) β) -> () β) (s-handler () h-check)))

(define-term wrap
  (Λ β (λ () f (unit -> (con) β) (H-check f))))
```
] <redex-shallow-compiler-wrapper>


== OCaml implementation

We have chosen OCaml as a base language to implement our contract system. The choice was purely because of two things. First, OCaml 5 has support for effect handlers built-in. Second, OCaml has a "macro system" that we can rely on to modify the program. On top of these two reasons is the author's familiarity with the language.

=== OCaml Attributes and Rewritters

OCaml does not have a clean "macro system". In fact, OCaml compilation chain allows users to introduce any rewritter defined as a source to source transformation. A rewritter can be any program that takes the whole file source, and returns a (modified) file source. Because there is no restriction, rewritters are free to modify, add, delete source code. However, useful rewritters will try to edit programs with intention. For this purpose, ppxlib#footnote(link("https://ocaml-ppx.github.io/ppxlib/ppxlib/index.html")), a common library is provided for writting rewritters, allowing them to parse and modify source code in Abstract Syntax Tree (AST) objects. OCaml syntax also support rewritters by providing a way to annotate source code places in AST through the use of _attributes_#footnote(link("https://ocaml.org/manual/5.5/attributes.html")). Attributes are enclosed in square brackets, tagged with an identifier and carry "code-like" payloads. Readers familiar with OCaml might have used attributes already, as one of the most commonly used attributes is `[@@deriving show]` to allow structs to be print-able.

=== OCaml Contracts as Attributes

Using attributes, we define contracts and our rewritter acts as the compiler as defined. Wrappers can be added manually or automatically with an attribute denoting the wrapper placement. The modified source code might use functions, objects that was not defined previously, therefore we expect users to include our library (`Conteff_lib`) where it contains all extra declarations for compilation and running. All running examples are defined under the header in @ocaml-header.

#figure(caption: "Header Declaration")[
```ocaml
open Conteff_lib
```
] <ocaml-header>

In @ocaml-contract-attributes is the list of some contract attributes syntax. Users attach these attributes to guard a value, function or variable with some contract `c`, which we discuss later on how to write different contract types. To install the wrapper, users only need to attach `%contract_main` to the expression that has contract checking code.

#figure(caption: "Attributes for Contracts", table(
  columns: 2,

  [Attributes], [Meaning],
  [`let[@contract c] x = e`], [Place contract `c` on value/function `x`],
  [`[%contract_main] e`], [Install the contract wrapper on `e`],
  [`let%contract_main f = e`], [Install the contract wrapper on `f`],
  [`[%mon c ~pos:p ~neg:n ~loc:j] e`], [Place contract `c` on `e` with explicit labels],
)) <ocaml-contract-attributes>

Our rewritter supports three main types of contracts, flat, functional, and dependent. Firstly, a flat contract is a function that takes a value and returns boolean. Secondly, since contracts can be nested far inside by the use of functional and dpendent contracts, the structured syntax is recursive: if `c_1,c_2` is a contract, then `c_1 @-> c_2` is a functional contract and `dep c_1 (fun x -> c_2)` is a dependent contract. During the writing of contracts, for brewvity, users can use identifiers to a functions in-scope during compilation, instead of writing the contract code in full.

Because OCaml is a curried-by-default language, we take that same approach to introduce contracts for multi-parameters functions. For functional contracts, the syntax is clear and precise. For dependent contract, the syntax creates a nested structure that is unnatural to the human eyes. We provide a different syntax for dependent contracts that is inspired by Racket's contract macro, `[@contract dep_args [(arg_1, c_1); ...] (fun arg_1 ... -> e)]`. The new syntax is purely for human users, it will be expanded into the nested structure accordingly during the rewriting process before compiling into contract checking code. Below is the example syntax for functional and dependent contracts annotation.

```ocaml
(* this is a functional contract *)
let [@contract c_1 @-> c_2 @-> c_3]
  f x y = e

(* this is a dependent contract *)
let [@contract dep c_1 (fun x -> (dep c_2 (fun y -> c_3)))]
  g x y = e

(* this is a dependent contract with a better syntax *)
let [@contract dep_args [(x,c_1); (y,c_2)] (fun x y -> c_3)]
  h x y = e
```

The macro unwraps functional and dependent contracts with lambdas until flat contract and simply convert it to an effect invocation. Accordingly to our formal model, there is only one effect, defined as in @ocaml-check-effect. Labels are automatically added, and during the lambdas unrolling, labels are swapped in the correct manner.

#figure(caption: [OCaml Contract Checking Effect])[
```ocaml
type label = string
type _ Effect.t +=
  | Check : { pos : label; loc : label; pred : 'a -> bool; value : 'a } -> 'a Effect.t
```
]<ocaml-check-effect>

=== Tuple Contracts

Tuple contracts are supported using `[%mon (contract_left, contract_right)]` attribute. It breaks down recursively into monitor(s) for left injection and monitor(s) for right injection and builds a new tuple. Because tuple elements are wrapped with monitors, tuple contracts work with functions as well.

@ocaml-tuple-contracts is a simple example over a tuple of function and value. Line 2 places a contract on the tuple, ensuring that the function returns a negative number. Its invocation on line 3 will blame because the function is returning a positive number.

#figure(caption: [Tuple Contracts])[
```ocaml
let is_neg n = n < 0 in
let f, v = [%mon (any @-> is_neg, is_neg)] (fun () -> 1, -1) in
(f ())
```
] <ocaml-tuple-contracts>

=== Boxes and Vectors Contracts

Our library provide two types `Box` and `Vector` that is native to our contract system. Users can write contracts on these types. Internally, they are represented as OCaml records of functions. A box is a record with two functions get and set as in @ocaml-box, and is created using `Box.create`. Users _should_ only use the box by its interface `Box.get` and `Box.set`. Because these are functions, a box contract `[%mon box contract]` attribute applies the functional contracts on the record's functions. Similarly for vectors, their records have three functions `length,get,set` as in @ocaml-vector and created by `Vector.create`, using a default value, or `Vector.of_list`, using a list as initializer. The interface is the three functions `Vector.length,Vector.get,Vector.set`. The vector contract `[%mon vector contract]` attribute applies the functional contracts on the record's functions.

#figure(caption: [OCaml Box])[
```ocaml
(* Box.ml *)
type 'a t = { get : unit -> 'a; set : 'a -> unit }
let get b = b.get ()
let set b v = b.set v
```
] <ocaml-box>


#figure(caption: [OCaml Vector])[
```ocaml
(* Vector.ml *)
type 'a t = { length : int; get : int -> 'a; set : int -> 'a -> unit }
let length v = v.length
let get v i = v.get i
let set v i x = v.set i x
let to_list v = List.init v.length v.get
```
] <ocaml-vector>

@ocaml-box-contract shows how box contract is used. Line 2 creates a box using `Box.create` applied to a initial value. This box is then protected by `[%mon box is_pos]`, therefore set must be applied with positive numbers, and get must return positive numbers. Line 3 calls `Box.set` with the protected box and a non-positive number. The contract catches and throws a blame.

#figure(caption: [Box Contracts])[
```ocaml
let is_pos n = n > 0 in
let b = [%mon box is_pos] (Box.create 1) in
Box.set b (-1);
```
] <ocaml-box-contract>

@ocaml-vector-contract shows how vector contract is used. Line 2 creates a vector using `Vector.create` to construct a vector of 3 values with default value `1`. This vector is protected under a contract `[%mon vector is_pos]` that ensures get/set vector elements are positive. Line 3 tries to set the vector's element at index 2 with a negative number. The contract catches and throws a blame.

#figure(caption: [Vector Contracts])[
```ocaml
let is_pos n = n > 0 in
let v = [%mon vector is_pos] (Vector.create 3 1)
Vector.set v 2 (-4))
```
] <ocaml-vector-contract>


=== States encoding contracts

Our OCaml model also implement contract states, which we briefly introduced in @compiler-formal-states. For this to work, we provide attributes to declare contract states, `%%contract_states`; and a wrapper attribute with states initialization, `%contract_main_states`. Declaring contract states are a series of let binding expressions, with their names, types and initial value. For each state declaration, the rewritter automatically generate two new effects, `%contract_get_*` and `%contract_set_*`. When writing the contracts, users can use these attributes to obtain or modify the states. Due to the limitation of OCaml rewritter, these states are only available when the whole program is in a single file if using `%contract_main_states`. Otherwise, users can manually write the wrapper to provide all possible states.


Because states are controlled using effects, and the macro system does not decouple contract effects from main program effects, users can call these effects. Technically, our rewritter can try to limit the usage of these `%contract_get_*,%contract_set_*` attributes to contract checking code if we can identify contract checking code. However, since contracts can be an identifier of some function, we find that distinction undesirable.

@ocaml-example-contract-states illustrates a simple example where a state is used to record inputs to the same function. Line 1 defines the contract state `previous` using `[%%contract_states]`. The rewritter takes the state definition and uses it to initialize the states in handler invocation at line 9 with `%contract_main_states`. Lines 2-7 define the contract code function `nondecreasing`. The contract function gets the state using `[%contract_get_previous]`, then checks it against the contract's input, if the input increases then sets the state using `[%contract_set_previous]` and returns true; otherwise returns false. Line 8 defines a function protected with a function contract having a domain contract as `nondecreasing`, ensuring the input to the function between each sequential calls is strictly increasing.

#figure(caption: "OCaml Implementation Contract States")[
```ocaml
[%%contract_states let previous : int option = None]
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

=== Effectful Contracts

We implemented Main-Effect Contracts using the attribute

`[@effect_contract EffectName (domain |> codomain)]`.

As previously discussed in @chapter-compiler, this is expanded into a handler capturing the effect `EffectName`, checking the domain contract, executing the effect again, and on effect returns, checking the codomain contract. This attribute is attached to a value $e$, which the rewritter converts into a _thunk_ `fun () -> e` and applies it to the handler. Upon running if the value executes a the captured effect, then it will be caught by the contract-installed-handler first.

@ocaml-example-contract-effect illustrates a simple example. Line 1 defines the effect `Identity`, with its handler in lines 2-9. Line 12 defines a function that is protected under an Main-Effect Contract. The effect invocation must satisfies the input contract `input_in_range` and `output_in_range`. These ranges have a misalignment to demonstrate cases where the effect's input failure, and effect's output failure.

#figure(caption: "OCaml Implementation Main-Effect Contracts")[
```ocaml
type _ Effect.t += Identity : int -> int Effect.t
let handle_identity body =
  Effect.Deep.try_with body ()
    { effc = (fun (type a) (eff : a Effect.t) ->
        match eff with
        | Identity n ->
            Some (fun (k : (a, _) Effect.Deep.continuation) ->
              Effect.Deep.continue k n)
        | _ -> None) }
let input_in_range n = 0 <= n && n <= 20
let output_in_range n = 10 <= n && n <= 30
let[@effect_contract Identity (input_in_range |> output_in_range)] checked n =
  Effect.perform (Identity n)
let scenario n =
  try
    let result = handle_identity (fun () -> checked n) in
  with Contract.Blame { party; contract } ->
    Printf.printf "  blame: %s (%s)\n" party contract
let%contract_main () =
  scenario 5;  (* Input passes, output fails. *)
  scenario 10; (* Both pass. *)
  scenario 15; (* Both pass. *)
  scenario 20; (* Both pass. *)
  scenario 25  (* Input fails. *)
```
] <ocaml-example-contract-effect>

Although we do not provide an implementation for Contract-Handlers Contracts, which separates the contract effects and provide scoping through handlers. The contract system implemented can implement the contract capabilities as described by @cameron2024effectful. There is a caveat that states are cleared intentionally, which should be handled nicely under scoped Contract-Handler Contracts. Below, we show how each capabilities are implemented under the OCaml implementation of our contract system with support for Main-Effect Contracts.

#rn("ALLOW CALL") A state is used to mark allowance across function calls.

#rn("EXCEPTIONS") Effects implement exceptions, and Main-Effect Contracts are used to constrains them.

#rn("FRAMING") Mutable boxes are implemented using effects with get/set operations over their box's index, and Main-Effect Contracts are used to control which box is allowed.

#rn("GHOST STATE") State bits are used, and accessible only to contracts.

#rn("MUST CALL") A state bit is used to mark called functions. Function required to call sets this bit.

#rn("NON-REENTRANCE") A state bit is used to mark entrance. Function contract sets this bit in domain contract, and unsets this bit in codomain contract.

#rn("PURE") Assumes that side-effects are modeled as effects, Main-Effect Contracts rejects every possible effects.

#rn("RESTRICTED EFFECTS") Assumes that side-effects are modeled as effects, Main-Effect Contracts rejects some effects.

#rn("TERMINATION") A state is used to track/monitor the input size.

#rn("UNION CONTRACTS") A state is used to track the checking state over higher-order contracts.
