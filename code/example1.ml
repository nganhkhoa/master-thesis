let any _ = true
let bigger_10 num = num > 10
let bigger_20 num = num > 20
let total_bigger_50 x v = (x + v) > 50

let [@contract : bigger_10] x : int = 9

let [@contract : bigger_10 -> bigger_20]
  f1 (x : int) : int = x

let [@contract : bigger_10 -> total_bigger_50 dep]
  f2 (x : int) : int = x

let pass g v =
  (* by the contract in f3, g must be bigger_10 -> bigger_20 *)
  let vv = g (v - 20) in
  vv > 30

let [@contract : any -> ((bigger_10 -> bigger_20) -> pass dep)]
  f3 (x : int) (g : int -> int) : int = g x
