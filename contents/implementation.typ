#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *

#import "/models/language.typ": *
#import "/proofs/setup.typ": *
#import "/utils.typ": load-bib, no-ref

#show: codly-init.with()
#codly(languages: codly-languages)

#show: no-ref

= Implementation

We implement the formal compiler model into OCaml, by adding a preprocessor. We utilize the OCaml attribute to add contract annotations to variables. The preprocessor rewrites annotated variables according to the compiler rules defined. Note that the compiler does not place a handler during compilation, but after the compilation. Because the handler must be installed around the whole program, more precisely, around everywhere the contract annotated variables are used. The developer can install the handler manually by invoking a predefined wrapper, or annotate a function as main and the preprocessor rewrites to add wrapper automatically.

Annotations are OCaml annotations. Although OCaml annotations support string-like payload, we find it better to use a OCaml type expression as payload to define contracts. Annotations are not code, therefore we cannot support first-order contracts, and use function names as predicates. In @ocaml-contract-example, we define the contract annotation syntax that developers can use to annotate their OCaml code with contracts.


#figure(caption:[OCaml Contract Annotation Example])[
```ocaml
(* flat contract *)
let [@contract : predicate] x : t = e

(* function contract
 * arguments are inside a tuple
 *)
let [@contract : (p1_pred * p2_pred) -> f_pred]
  f (p1 : t1) (p2 : t2) : t = f_body

(* dependent function contract
 * similarly to function contract, annotated with as 'dep
 *)
let [@contract : (p1_pred * p2_pred) -> g_pred as 'dep]
  g (p1 : t1) (p2 : t2) : t = g_body

(* tuple contract
 * using tuple syntax and annotated with as 'tuple
 *)
let [@contract : (t1_pred * t2_pred) as 'tuple]
  tup : (t1 * t2) = (e, e)
```
] <ocaml-contract-example>

The preprocessor rewrite using the compiler rules. All flat contracts are compiled into a single effect, formally it is #effcheck, implementation wise we define a name `Contract.Check`.

```ocaml
module Contract = struct
type _ Effect.t +=
  | Check : (string * ('a -> bool) * 'a) -> 'a Effect.t
end
```

$kw("wrap")$ is defined similarly in OCaml, we remove the type annotations for clarity.

```ocaml
let rec wrap thunk =
  Effect.Deep.match_with thunk ()
  {
    Effect.Deep.retc = (fun x -> x);
    exnc = (fun e -> raise e);
    effc = fun eff ->
      let open Effect.Deep in
      match eff with
      | Flat (label, check, arg) ->
          Some (fun k ->
            let ok = wrap (fun () -> check arg) in
            if ok
            then continue k arg
            else discontinue k (Blame label))
      | _ -> None
  }
```

== Contract States and Interaction

=== Global State

Because the entire program is wrapped into a single handler for all effects, we can unify a single state for effects only. Predicates must now receive an extra argument, which is the context. The $kw("wrap")$ function is now defined with an extra argument current context, and it returns the result and updated context. At the callsite, it is provided with the initial value. States are provided to the handler, therefore the handler provide two effects to get and set the state.

```ocaml
type state = int
let state_init = 0

let rec wrap_inner : type r. (unit -> r) -> state -> r * state =
  fun thunk init ->
  match_with thunk ()
  {
    retc = (fun x state -> (x, state));
    exnc = (fun e _state -> raise e);
    effc = fun (type a) (eff : a Effect.t) ->
      let handle_eff : ((a, state -> r * state) continuation -> state -> r * state) option =
      match eff with
      | Get -> Some (fun k state -> continue k state state)
      | Set x -> Some (fun k _state -> continue k () x)
      | Flat (label, check, arg) ->
          Some (fun k state ->
            let (ok, updated_state) = wrap_inner (fun () -> check arg) state in
            if ok
            then continue k arg updated_state
            else discontinue k (Blame label) updated_state)

      | _ -> None
    in
    handle_eff
  }
  init

let wrap main =
  let r, _ = wrap_inner main state_init in
  r

let () = wrap main
```

This approach works, but with a small caveat. Main code can access this state, and can potentially modifies the contract's state. This issue is easily resolved by making two more handlers, one handler for state, and one handler perform recursive wrapping for contract checking code. The state handler is installed in the main wrapper, placing on the top most contract checking code. When a contract check occurs it opens a new scope, starting with the current state. All dependent contract checking code originates from this top most contract update on the same state. Once the top most contract code returns, the state is updated at the continuation of the main wrapper. Because the state is registered by the main wrapper, and the handler for state is registered only when contract checking code executes, main code has no access to this state.

However, in this implementation, a `Flat` effect might be invoked arbitrarily by the main code. In an actual language implementation, we suggest this effect be private, or a special keyword to prevent developers interact with the effect state.

```ocaml
let rec with_state : type res. (unit -> res) -> int -> res * int =
  fun thunk init ->
  match_with thunk ()
  { retc = (fun x s -> (x, s));
    exnc = (fun e _ -> raise e);
    effc = fun (type a) (eff : a Effect.t) ->
      let handler : ((a, int -> res * int) continuation -> int -> res * int) option =
        match eff with
        | Get -> Some (fun k s -> continue k s s)
        | Set x -> Some (fun k _ -> continue k () x)
        | _ -> None
      in handler
  } init

let rec wrap_inner : type res. (unit -> res) -> res =
  fun thunk ->
  match_with thunk ()
  { retc = (fun x -> x);
    exnc = (fun e -> raise e);
    effc = fun (type a) (eff : a Effect.t) ->
      match eff with
      | Flat (label, check, arg) ->
          Some (fun k ->
            let ok = wrap_inner (fun () -> check arg) in
            if ok then continue k arg
            else discontinue k (Blame label))
      | _ -> None
  }

let rec wrap : type res. (unit -> res) -> int -> res * int =
  fun thunk init ->
  match_with thunk ()
  { retc = (fun x s -> (x, s));
    exnc = (fun e _ -> raise e);
    effc = fun (type a) (eff : a Effect.t) ->
      let handler : ((a, int -> res * int) continuation -> int -> res * int) option =
        match eff with
        | Flat (label, check, arg) ->
            Some (fun k current_state ->
              let (ok, next_state) =
                with_state (fun () -> wrap_inner (fun () -> check arg)) current_state
              in
              if ok then continue k arg next_state
              else discontinue k (Blame label) next_state)
        | _ -> None
      in handler
  } init
```

== Contract Interaction

All contract are unified under a single context. This context is accessible through two effects `Get` and `Set`. Let this context be a simple key-value storage, then programmers can devise complicated schemes to track function calls, current function scope, internal contract state, etc, ...
