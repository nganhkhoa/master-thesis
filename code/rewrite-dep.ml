(* original program *)
let [@contract : xpred -> outpred dep]
  f (x : x_type) : f_type = body


(* rewritten program *)
let f pos neg cloc (x : x_type) : f_type =
  let [@contract : xpred] x : x_type = x in
  let x_dep = x neg cloc cloc in
  let x = x neg pos cloc in

  let outpred_dep = outpred x_dep in
  let [@contract : outpred_dep] ret : f_type = body in
  ret pos neg cloc

