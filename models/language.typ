#import "/setup.typ": setupdoc
#show: setupdoc

#let contract-color = rgb("#0071BC")
#let effect-color = rgb("#F26035")

#let ckw(it) = text(fill: contract-color, weight: "regular", math.sans(it))
#let ekw(it) = text(fill: effect-color, weight: "bold", math.mono(it))
#let ctxt(it) = text(weight: "regular", math.sans(it))
#let etxt(it) = text(weight: "bold", math.mono(it))
#let kw(it) = text(fill: rgb("#333333"), weight: "regular", math.sans(it))

// Compiler and handler modes.
#let d = [d]
#let s = [s]
#let l = [l]

#let numt = $kw("num")$
#let boolt = $kw("bool")$
#let trueb = $kw("true")$
#let falseb = $kw("false")$
#let unit = $kw("unit")$
#let loc = $kw("loc")$

#let mtstore = $emptyset$
#let store = $sigma$

#let apply(a, b) = $#a med #b$

#let tuple(a,b) = $chevron.l #a,#b chevron.r$
#let injl(e) = $kw("inj.l")(#e)$
#let injr(e) = $kw("inj.r")(#e)$

#let ref(tau) = $kw("ref")(#tau)$
#let refc(tau) = $ckw("ref/c")(#tau)$
#let iszero(e) = $kw("zero?")(#e)$
#let newcell(e) = $kw("new")(#e)$
#let getcell(e) = $kw("get")(#e)$
#let setcell(e1,e2) = $kw("set")(#e1,#e2)$

#let newcell1(e) = $apply(kw("newcell"),#e)$
#let getcell1(e) = $apply(kw("getcell"), #e)$
#let setcell1(e1,e2) = $apply(apply(kw("setcell"),#e1),#e2)$

#let getstate() = $ckw("get")^scr("S")()$
#let modifystate(op,e) = $ckw("modify")^scr("S")(#op,#e)$

#let con(tau) = $ckw("con")(#tau)$
#let mon(k, l, j, kappa, e) = $ckw("mon")_#j^(#k,#l) (#kappa, #e)$
#let blame(l, p) = $attach(ckw("blame"), tr: #l, br: #p)$
#let check(k, j, e, v) = $ckw("check")_#j^#k (#e, #v)$
#let flat(e) = $ckw("flat")(#e)$
#let dep(kappa_1,kappa_2) = $#kappa_1 attach(->, br: i) #kappa_2$
#let cabs(x,e) = $ckw(lambda) #x . #e$ // freely add types or no types
#let ehandle(h, e, m: d, eff: none) = {
  if eff != none {
    $ekw("handle")^(#eff)_#m (#h,#e)$
  } else {
    $ekw("handle")_#m (#h,#e)$
  }
}
#let eperform(op, tau: none, eff: none) = {
  if tau != none {
    $ekw("perform")^#eff #op #tau$
  } else {
    $ekw("perform") #op$
  }
}
#let eapply(a, b) = $#a med #b$
#let ife(c,t,f) = $"if" #c "then" #t "else" #f$
#let guard(v, c, k, l, j) = $attach(ckw("guard"), tr: #k\,#l, br: #j)(#c, #v)$

#let eif(c, t, f) = $#base-kw("if") #c #base-kw("then") #t #base-kw("else") #f$

#let d = [d]
#let s = [s]
#let l = [l]

#let mteff = $chevron.l chevron.r$
#let effs(..l) = $chevron.l #l.pos().join([, ]) chevron.r$
#let eff = ekw("eff")
#let lab = ekw("lab")
#let blab = ekw("blab")
#let eblame(p) = $attach(ekw("error"), br: #p)$
// Every handler records its resumption mode: `d` (deep) or `s` (shallow).
// Deep is the default so existing figures remain compact; a shallow use writes
// `m: s`.  The rendered syntax always displays the mode as the first argument.
#let handler(h, m: d, eff: none) = {
  if eff != none {
    $ekw("handler")^(#eff)_(#m) (#h)$
  } else {
    $ekw("handler")_(#m) (#h)$
  }
}
#let handle(h, e, m: d, eff: none) = {
  if eff != none {
    $ekw("handle")^(#eff)_#m (#h,#e)$
  } else {
    $ekw("handle")_#m (#h,#e)$
  }
}

#let perform(op, tau: none, eff: none) = {
  if tau != none {
    $ekw("perform")^(#eff) #op #tau$
  } else {
    $ekw("perform") #op$
  }
}

#let teff(tau_1,epsilon,tau_2) = $#tau_1 attach(->,tr:#epsilon) #tau_2$

#let bop(E) = $ekw("bop")(#E)$

#let step = $-->$
#let step1 = $attach(step, tr: *)$
#let stepx = $arrow.r.dashed$
#let stepx1 = $attach(stepx, tr: *)$
#let cstep = $arrow.r.open$
#let cstep1 = $attach(cstep, tr: *)$
#let cstepx = $arrow.r.dotted$
#let cstepx1 = $attach(cstepx, tr:*)$
#let estep = $arrow.r.double.long$
#let estep1 = $attach(arrow.r.double.long, tr: *)$
#let estepx = $arrow.r.filled$
#let estepx1 = $attach(estepx, tr: *)$
#let compiles-into = $arrow.r.tail$

#let langb = $kw("Base")$
#let langc = $ckw("Contracts")$
#let langcs = $ckw("Contracts")^scr("S")$
#let lange = $ekw("Effects")$

#let type(ctx,e,t,eff: none,type: none) = {
  if type != none and eff == none {
    $#ctx attach(tack.r.short, br: type) #e : #t$
  } else if type != none and eff != none {
    $#ctx attach(tack.r.short, br: type) #e : #t | #eff$
  } else if type == none and eff != none {
    $#ctx tack.r.short #e : #t | #eff$
  } else {
    $#ctx tack.r.short #e : #t$
  }
}

#let effcheck = $#text(fill: rgb("#009E73"), weight: "regular", math.scr("C"))$
#let effstate = $#text(fill: rgb("#009E73"), weight: "regular", math.scr("S"))$
#let effstateget = $#text(fill: rgb("#009E73"), weight: "regular", math.scr("G"))$
#let effstateset = $#text(fill: rgb("#009E73"), weight: "regular", math.scr("M"))$
#let heffcheck = $ekw("h")_effcheck$
#let heffstate = $ekw("h")_effstate$
// Compilation derivations record the compiler variant above the arrow:
// d = deep, s = shallow, l = local. Deep is the default for generic rules.
#let compile(src, target, m: d) = {
  $#src med attach(arrow.r.tail, tr: #m) med #target$
}
#let typecompile(t) = $#t^*$


#let underline(color, it) = box(stroke: (bottom: 1pt + color), outset: (bottom: 2pt, left: 0pt, right: 0pt), $it$)
