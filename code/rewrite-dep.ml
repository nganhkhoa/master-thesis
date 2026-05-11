(* original program *)
let [@contract :
    (xpred * (gp1_p1_pred -> gp1_pred) -> gpred as 'dep) -> outpred as 'dep]
  f (x : x_type) (g : g_type) : f_type = body


(* rewritten program *)
let f pos neg cloc (x : x_type) (g : g_type) : f_type =
  let [@contract : xpred] x : x_type = x in
  let x_dep = x neg cloc cloc in
  let x = x neg pos cloc in

  let [@contract : (gp1_p1_pred -> gp1_pred) -> gpred as 'dep]
    g (g_p1 : gp1_intype) : g_outtype = g g_p1 in
  let g_dep =
    fun p1 -> Contract.run_with_effects (fun () -> g neg cloc cloc p1) in
  let g = g neg pos cloc in

  let outpred_dep = outpred x_dep g_dep in
  let [@contract : outpred_dep] ret : f_type = body in
  ret pos neg cloc

