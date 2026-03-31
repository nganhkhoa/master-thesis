(* original program *)
let [@contract : xpred -> ypred -> zpred -> outpred]
  f1 (x : x_type) (y : y_type) (z : z_type) : f_type = body

let [@contract : (g_inpred -> g_outpred) -> outpred]
  f2 (g : g_intype -> g_outtype) : f_type = body


(* rewritten program *)
let f1 pos neg cloc (x : x_type) (y : y_type) (z : z_type) : f_type =
  let [@contract : xpred] x : x_type = x in
  let x = x neg pos cloc in
  let [@contract : ypred] y : y_type = y in
  let y = y neg pos cloc in
  let [@contract : zpred] z : z_type = z in
  let z = z neg pos cloc in
  let [@contract : outpred] ret : f_type = body in
  ret pos neg cloc

let f2 pos neg cloc (g : g_intype -> g_outtype) : f_type =
  let [@contract : g_inpred -> g_outpred]
    g (g_p1 : g_intype) : g_outtype = g in
  let g = g neg pos cloc in
  let [@contract : outpred] ret : f_type = body in
  ret pos neg cloc
