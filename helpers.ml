(** Helper functions for making new ts-expressions from old ts-expressions. *)

open Typesystem
open Names

let lambda1 v x = LAMBDA(v,Phi x)
let lambda2 v1 v2 x = LAMBDA(v1,LAMBDA(v2,Phi x))
let lambda3 v1 v2 v3 x = LAMBDA(v1,LAMBDA(v2,LAMBDA(v3,Phi x)))

let to_atomic e = List.map (fun x -> Phi x) e

let make_Var c = Var c

let make_UU h a = APPLY(U h, a)
let make_TT h a = APPLY(T h, a)
let make_OO h a = APPLY(O h, a)

let make_Variable x = var_to_ts x
let make_TT_El x = make_TT T_El [Phi  x]
let make_TT_U x = make_TT T_U [Phi  x]
let make_TT_Pi    t1 (x,t2) = make_TT T_Pi    [Phi t1; lambda1 x t2]
let make_TT_Sigma t1 (x,t2) = make_TT T_Sigma [Phi t1; lambda1 x t2]
let make_TT_Pt = make_TT T_Pt []
let make_TT_Coprod t t' = make_TT T_Coprod [Phi t;Phi t']
let make_TT_Coprod2 t t' (x,u) (x',u') o = make_TT T_Coprod2 [Phi t; Phi t'; lambda1 x u; lambda1 x' (u'); o]
let make_TT_Empty = make_TT T_Empty []
let make_TT_IP tA a (x,tB,(y,tD,(z,q))) = make_TT T_IP [Phi tA; Phi a; lambda1 x tB; lambda2 x y tD; lambda3 x y z q]
let make_TT_Id t x y = make_TT T_Id [Phi t;Phi x;Phi y]
let make_OO_u m = make_OO O_u [Phi m]
let make_OO_j m n = make_OO O_j [Phi m; Phi n]
let make_OO_ev f p (v,t) = make_OO O_ev [Phi f;Phi p;lambda1 v t]
let make_OO_lambda t (v,p) = make_OO O_lambda [Phi t; lambda1 v p]
let make_OO_forall m m' n (v,o') = make_OO O_forall [Phi m;Phi m';Phi n;lambda1 v (o')]
let make_OO_pair a b (x,t) = make_OO O_pair [Phi a;Phi b;lambda1 x t]
let make_OO_pr1 t (x,t') o = make_OO O_pr1 [Phi t;lambda1 x (t'); o]
let make_OO_pr2 t (x,t') o = make_OO O_pr2 [Phi t;lambda1 x (t'); o]
let make_OO_total m1 m2 o1 (x,o2) = make_OO O_total [Phi m1;Phi m2;Phi o1;lambda1 x o2]
let make_OO_pt = make_OO O_pt []
let make_OO_pt_r o (x,t) = make_OO O_pt_r [Phi o;lambda1 x t]
let make_OO_tt = make_OO O_tt []
let make_OO_coprod m1 m2 o1 o2 = make_OO O_coprod [Phi m1; Phi m2; Phi o1; Phi o2]
let make_OO_ii1 t t' o = make_OO O_ii1 [t;t';o]
let make_OO_ii2 t t' o = make_OO O_ii2 [t;t';o]
let make_OO_sum tT tT' s s' o (x,tS) = make_OO O_sum [Phi tT; Phi tT'; Phi s; Phi s'; Phi o; lambda1 x tS]
let make_OO_empty = make_OO O_empty []
let make_OO_empty_r t o = make_OO O_empty_r [t; o]
let make_OO_c tA a (x,tB,(y,tD,(z,q))) b f = make_OO O_c [
  a; lambda1 x tB;
  lambda2 x y tD;
  lambda3 x y z q ]
let make_OO_ip_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_OO O_ip_r [
  tA; a;
  lambda1 x tB; lambda2 x y tD; lambda3 x y z q;
  i; lambda2  x' v tS; t]
let make_OO_ip m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_OO O_ip [
  Phi m1; Phi m2; Phi m3;
  Phi oA; Phi a;
  lambda1 x oB; lambda2 x y oD; lambda3 x y z q ]
let make_OO_paths m t x y = make_OO O_paths [Phi m; Phi t; Phi x; Phi y]
let make_OO_refl t o = make_OO O_refl [Phi t; Phi o]
let make_OO_J tT a b q i (x,(e,tS)) = make_OO O_J [Phi tT; Phi a; Phi b; Phi q; Phi i; lambda2 x e tS]
let make_OO_rr0 m2 m1 s t e = make_OO O_rr0 [Phi m2; Phi m1; Phi s; Phi t; Phi e]
let make_OO_rr1 m a p = make_OO O_rr1 [Phi m; Phi a; Phi p]
