(* original program *)
let [@contract : predicate] var : v_type = value

(* rewritten program *)
let var pos neg cloc =
  let module Contract = struct
    type _ Effect.t += V : v_type -> v_type Effect.t
  end in

  let handler =
    {
      effc = fun (type e) (eff : e Effect.t) ->
        match eff with
        | Contract.V x -> Some (fun k ->
            if predicate x
            then continue k x
            else discontinue k (Blame pos)
          )
        | _ -> None
    }
  in

  try_with (fun () ->
    Effect.perform (Contract.V value);
  ) ()
  handler
