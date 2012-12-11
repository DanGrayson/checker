(** Helper functions for dealing with expressions. *)

open Error
open Variables
open Typesystem
open Names

let cite_tactic tac args = APPLY(TAC tac, args)

let ( ** ) x s = ARG(x,s)		(* right associative *)

let rec join_args a b =
  match a with
  | ARG(x,a) -> ARG(x,join_args a b)
  | FST a -> FST(join_args a b)
  | SND a -> SND(join_args a b)
  | NIL -> b

let rec list_to_spine = function
  | x :: a -> x ** list_to_spine a
  | [] -> NIL

let rec arg_exists p args =
  match args with
  | ARG(x,a) -> p x || arg_exists p a
  | FST a | SND a -> arg_exists p a
  | NIL -> false

let rec args_length = function
  | FST a | SND a | ARG(_,a) -> 1 + args_length a
  | NIL -> 0

let rec args_equal eq args args' =
  match (args,args') with
  | ARG(x,args), ARG(x',args') -> eq x x' && args_equal eq args args'
  | FST args, FST args' -> args_equal eq args args'
  | SND args, SND args' -> args_equal eq args args'
  | NIL, NIL -> true
  | _ -> false

let args_fold f pi1 pi2 accu args = (* it's fold_left, which is the only direction that makes sense *)
  let rec repeat accu args =
    match args with
    | ARG(a,args) -> repeat (f accu a) args
    | FST args -> repeat (pi1 accu) args
    | SND args -> repeat (pi2 accu) args
    | NIL -> accu
  in repeat accu args

let pi1 = function
  | pos, APPLY(h,args) -> (pos,APPLY(h,join_args args (FST NIL)))
  | pos, PAIR(x,_) -> x
  | _ -> raise Internal

let pi2 = function
  | pos, APPLY(h,args) -> (pos,APPLY(h,join_args args (SND NIL)))
  | pos, PAIR(_,y) -> y
  | _ -> raise Internal

(** Helper functions for making new ts-expressions from old ts-expressions. *)

let lambda1 v x = nowhere 55 (LAMBDA(v, x))
let lambda2 v1 v2 x = lambda1 v1 (lambda1 v2 x)
let lambda3 v1 v2 v3 x = lambda1 v1 (lambda2 v2 v3 x)

let make_Var c = Var c

let make_U h a = APPLY(U h, a)
let make_T h a = APPLY(T h, a)
let make_O h a = APPLY(O h, a)

let make_Variable x = var_to_ts x
let make_U_next x = make_U U_next (x ** NIL)
let make_U_max x y = make_U U_max (x **  y ** NIL)
let make_T_El x = make_T T_El (x ** NIL)
let make_T_U x = make_T T_U ( x ** NIL)
let make_T_Pi    t1 (x,t2) = make_T T_Pi    (t1 ** lambda1 x t2 ** NIL)
let make_T_Sigma t1 (x,t2) = make_T T_Sigma (t1 ** lambda1 x t2 ** NIL)
let make_T_Pt = make_T T_Pt NIL
let make_T_Coprod t t' = make_T T_Coprod (t ** t' ** NIL)
let make_T_Coprod2 t t' (x,u) (x',u') o = make_T T_Coprod2 (t ** t'** lambda1 x u ** lambda1 x' (u')** o ** NIL)
let make_T_Empty = make_T T_Empty NIL
let make_T_IP tA a (x,tB,(y,tD,(z,q))) = make_T T_IP (tA ** a ** lambda1 x tB ** lambda2 x y tD ** lambda3 x y z q ** NIL)
let make_T_Id t x y = make_T T_Id (t **x **y ** NIL)
let make_O_u m = make_O O_u (m ** NIL)
let make_O_j m n = make_O O_j (m ** n ** NIL)
let make_O_ev f p (v,t) = make_O O_ev (f **p **lambda1 v t ** NIL)
let make_O_lambda t (v,p) = make_O O_lambda (t ** lambda1 v p ** NIL)
let make_O_forall m m' n (v,o') = make_O O_forall (m **m'**n **lambda1 v (o') ** NIL)
let make_O_pair a b (x,t) = make_O O_pair (a **b **lambda1 x t ** NIL)
let make_O_pr1 t (x,t') o = make_O O_pr1 (t **lambda1 x (t')** o ** NIL)
let make_O_pr2 t (x,t') o = make_O O_pr2 (t **lambda1 x (t')** o ** NIL)
let make_O_total m1 m2 o1 (x,o2) = make_O O_total (m1 **m2 **o1 **lambda1 x o2 ** NIL)
let make_O_pt = make_O O_pt NIL
let make_O_pt_r o (x,t) = make_O O_pt_r (o **lambda1 x t ** NIL)
let make_O_tt = make_O O_tt NIL
let make_O_coprod m1 m2 o1 o2 = make_O O_coprod (m1 ** m2 ** o1 ** o2 ** NIL)
let make_O_ii1 t t' o = make_O O_ii1 (t **t'**o ** NIL)
let make_O_ii2 t t' o = make_O O_ii2 (t **t'**o ** NIL)
let make_O_sum tT tT' s s' o (x,tS) = make_O O_sum (tT ** tT'** s ** s'** o ** lambda1 x tS ** NIL)
let make_O_empty = make_O O_empty NIL
let make_O_empty_r t o = make_O O_empty_r (t ** o ** NIL)
let make_O_c tA a (x,tB,(y,tD,(z,q))) b f = make_O O_c ( 
  a ** lambda1 x tB ** lambda2 x y tD ** lambda3 x y z q  ** NIL)
let make_O_ip_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_O O_ip_r (
  tA ** a ** lambda1 x tB ** lambda2 x y tD ** lambda3 x y z q ** i ** lambda2  x' v tS ** t ** NIL)
let make_O_ip m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_O O_ip (
  m1 ** m2 ** m3 ** oA ** a ** lambda1 x oB ** lambda2 x y oD ** lambda3 x y z q  ** NIL)
let make_O_paths m t x y = make_O O_paths (m ** t ** x ** y ** NIL)
let make_O_refl t o = make_O O_refl (t ** o ** NIL)
let make_O_J tT a b q i (x,(e,tS)) = make_O O_J (tT ** a ** b ** q ** i ** lambda2 x e tS ** NIL)
let make_O_rr0 m2 m1 s t e = make_O O_rr0 (m2 ** m1 ** s ** t ** e ** NIL)
let make_O_rr1 m a p = make_O O_rr1 (m ** a ** p ** NIL)
