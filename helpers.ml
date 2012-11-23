(** Helper functions for making expressions. *)

open Typesystem

let make_Var c = Var c
let make_UU h a = APPLY(UU h, a)
let make_TT h a = APPLY(TT h, a)
let make_OO h a = APPLY(OO h, a)
let make_Variable x = Variable x
let make_LAM v x = LAMBDA(v,x)
let make_LAM2 v1 v2 x = make_LAM v1 (make_LAM v2 x)
let make_LAM3 v1 v2 v3 x = make_LAM v1 (make_LAM2 v2 v3 x)
let make_TT_El x = make_TT TT_El [x]
let make_TT_U x = make_TT TT_U [x]
let make_TT_Pi    t1 (x,t2) = make_TT TT_Pi    [t1; make_LAM x t2]
let make_TT_Sigma t1 (x,t2) = make_TT TT_Sigma [t1; make_LAM x t2]
let make_TT_Pt = make_TT TT_Pt []
let make_TT_Coprod t t' = make_TT TT_Coprod [t;t']
let make_TT_Coprod2 t t' (x,u) (x',u') o = make_TT TT_Coprod2 [t; t'; make_LAM x u; make_LAM x' (u'); o]
let make_TT_Empty = make_TT TT_Empty []
let make_TT_IC tA a (x,tB,(y,tD,(z,q))) = make_TT TT_IC [tA; a; make_LAM x tB; make_LAM2 x y tD; make_LAM3 x y z q]
let make_TT_Id t x y = make_TT TT_Id [t;x;y]
let make_OO_u m = make_OO OO_u [m]
let make_OO_j m n = make_OO OO_j [m; n]
let make_OO_ev f p (v,t) = make_OO OO_ev [f;p;make_LAM v t]
let make_OO_ev_hole f p = make_OO OO_ev [f;p] (* fill in third argument later *)
let make_OO_lambda t (v,p) = make_OO OO_lambda [t; make_LAM v p]
let make_OO_forall m m' n (v,o') = make_OO OO_forall [m;m';n;make_LAM v (o')]
let make_OO_pair a b (x,t) = make_OO OO_pair [a;b;make_LAM x t]
let make_OO_pr1 t (x,t') o = make_OO OO_pr1 [t;make_LAM x (t'); o]
let make_OO_pr2 t (x,t') o = make_OO OO_pr2 [t;make_LAM x (t'); o]
let make_OO_total m1 m2 o1 (x,o2) = make_OO OO_total [m1;m2;o1;make_LAM x o2]
let make_OO_pt = make_OO OO_pt []
let make_OO_pt_r o (x,t) = make_OO OO_pt_r [o;make_LAM x t]
let make_OO_tt = make_OO OO_tt []
let make_OO_coprod m1 m2 o1 o2 = make_OO OO_coprod [m1; m2; o1; o2]
let make_OO_ii1 t t' o = make_OO OO_ii1 [t;t';o]
let make_OO_ii2 t t' o = make_OO OO_ii2 [t;t';o]
let make_OO_sum tT tT' s s' o (x,tS) = make_OO OO_sum [tT; tT'; s; s'; o; make_LAM x tS]
let make_OO_empty = make_OO OO_empty []
let make_OO_empty_r t o = make_OO OO_empty_r [t; o]
let make_OO_c tA a (x,tB,(y,tD,(z,q))) b f = make_OO OO_c [
  a; make_LAM x tB;
  make_LAM2 x y tD;
  make_LAM3 x y z q ]
let make_OO_ic_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_OO OO_ic_r [
  tA; a;
  make_LAM x tB; make_LAM2 x y tD; make_LAM3 x y z q;
  i; make_LAM2  x' v tS; t]
let make_OO_ic m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_OO OO_ic [
  m1; m2; m3;
  oA; a;
  make_LAM x oB; make_LAM2 x y oD; make_LAM3 x y z q ]
let make_OO_paths m t x y = make_OO OO_paths [m; t; x; y]
let make_OO_refl t o = make_OO OO_refl [t; o]
let make_OO_J tT a b q i (x,(e,tS)) = make_OO OO_J [tT; a; b; q; i; make_LAM x (make_LAM e tS)]
let make_OO_rr0 m2 m1 s t e = make_OO OO_rr0 [m2; m1; s; t; e]
let make_OO_rr1 m a p = make_OO OO_rr1 [m; a; p]
let make_Defapp name u t o =  APPLY(Defapp name, List.flatten [u;t;o])
