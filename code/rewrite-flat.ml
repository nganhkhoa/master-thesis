(* original program *)
let [@contract : predicate] var : v_type = value

(* rewritten program *)
let var pos neg cloc =
  Effect.perform (Contract.Flat (pos, predicate, value));
