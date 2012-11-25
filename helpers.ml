(** Helper functions for making expressions. *)

open Typesystem

let make_Var c = Var c
let make_UU h a = APPLY(U h, a)
let make_TT h a = APPLY(T h, a)
let make_OO h a = APPLY(O h, a)
let make_Variable x = Variable x
let make_LAM v x = LAMBDA(v,x)
let make_LAM2 v1 v2 x = make_LAM v1 (make_LAM v2 x)
let make_LAM3 v1 v2 v3 x = make_LAM v1 (make_LAM2 v2 v3 x)
let make_TT_El x = make_TT T_El [x]
let make_TT_U x = make_TT T_U [x]
let make_TT_Pi    t1 (x,t2) = make_TT T_Pi    [t1; make_LAM x t2]
let make_TT_Sigma t1 (x,t2) = make_TT T_Sigma [t1; make_LAM x t2]
let make_TT_Pt = make_TT T_Pt []
let make_TT_Coprod t t' = make_TT T_Coprod [t;t']
let make_TT_Coprod2 t t' (x,u) (x',u') o = make_TT T_Coprod2 [t; t'; make_LAM x u; make_LAM x' (u'); o]
let make_TT_Empty = make_TT T_Empty []
let make_TT_IC tA a (x,tB,(y,tD,(z,q))) = make_TT T_IC [tA; a; make_LAM x tB; make_LAM2 x y tD; make_LAM3 x y z q]
let make_TT_Id t x y = make_TT T_Id [t;x;y]
let make_OO_u m = make_OO O_u [m]
let make_OO_j m n = make_OO O_j [m; n]
let make_OO_ev f p (v,t) = make_OO O_ev [f;p;make_LAM v t]
let make_OO_lambda t (v,p) = make_OO O_lambda [t; make_LAM v p]
let make_OO_forall m m' n (v,o') = make_OO O_forall [m;m';n;make_LAM v (o')]
let make_OO_pair a b (x,t) = make_OO O_pair [a;b;make_LAM x t]
let make_OO_pr1 t (x,t') o = make_OO O_pr1 [t;make_LAM x (t'); o]
let make_OO_pr2 t (x,t') o = make_OO O_pr2 [t;make_LAM x (t'); o]
let make_OO_total m1 m2 o1 (x,o2) = make_OO O_total [m1;m2;o1;make_LAM x o2]
let make_OO_pt = make_OO O_pt []
let make_OO_pt_r o (x,t) = make_OO O_pt_r [o;make_LAM x t]
let make_OO_tt = make_OO O_tt []
let make_OO_coprod m1 m2 o1 o2 = make_OO O_coprod [m1; m2; o1; o2]
let make_OO_ii1 t t' o = make_OO O_ii1 [t;t';o]
let make_OO_ii2 t t' o = make_OO O_ii2 [t;t';o]
let make_OO_sum tT tT' s s' o (x,tS) = make_OO O_sum [tT; tT'; s; s'; o; make_LAM x tS]
let make_OO_empty = make_OO O_empty []
let make_OO_empty_r t o = make_OO O_empty_r [t; o]
let make_OO_c tA a (x,tB,(y,tD,(z,q))) b f = make_OO O_c [
  a; make_LAM x tB;
  make_LAM2 x y tD;
  make_LAM3 x y z q ]
let make_OO_ic_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_OO O_ic_r [
  tA; a;
  make_LAM x tB; make_LAM2 x y tD; make_LAM3 x y z q;
  i; make_LAM2  x' v tS; t]
let make_OO_ic m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_OO O_ic [
  m1; m2; m3;
  oA; a;
  make_LAM x oB; make_LAM2 x y oD; make_LAM3 x y z q ]
let make_OO_paths m t x y = make_OO O_paths [m; t; x; y]
let make_OO_refl t o = make_OO O_refl [t; o]
let make_OO_J tT a b q i (x,(e,tS)) = make_OO O_J [tT; a; b; q; i; make_LAM x (make_LAM e tS)]
let make_OO_rr0 m2 m1 s t e = make_OO O_rr0 [m2; m1; s; t; e]
let make_OO_rr1 m a p = make_OO O_rr1 [m; a; p]
let make_Defapp name u t o =  APPLY(Defapp(name,0), List.flatten [u;t;o])
