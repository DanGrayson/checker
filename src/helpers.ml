(** Helper functions for dealing with expressions. *)

open Error
open Variables
open Typesystem
open Names

let isunused_variable_expression x = 
  match unmark x with 
  | APPLY(V v, END) -> isunused v
  | _ -> false

let cite_tactic tac args = APPLY(TAC tac, args)

let ( ** ) x s = ARG(x,s)		(* right associative *)

let rec nth_arg n args =
  match n,args with
  | 0, ARG(x,_) -> x
  | n, CAR args | n, CDR args -> nth_arg n args
  | _, END -> raise Not_found
  | n, ARG(_,args) -> nth_arg (n-1) args

let rec join_args a b =
  if b = END then a else
  match a with
  | ARG(x,a) -> ARG(x,join_args a b)
  | CAR a -> CAR(join_args a b)
  | CDR a -> CDR(join_args a b)
  | END -> b

let join_args_rev a b =
  let rec repeat a b =
    match a with
    | ARG(x,a) -> repeat a (ARG(x,b))
    | CAR a -> repeat a (CAR b)
    | CDR a -> repeat a (CDR b)
    | END -> b
in repeat a b

let reverse_spine a = join_args_rev a END

let rec args_compare expr_compare a b =
  match (a,b) with
  | ARG(x,a), ARG(y,b) -> expr_compare x y && args_compare expr_compare a b
  | CAR a, CAR b -> args_compare expr_compare a b
  | CDR a, CDR b -> args_compare expr_compare a b
  | END, END -> true
  | _ -> false

let rec list_to_spine = function
  | x :: a -> x ** list_to_spine a
  | [] -> END

type spine_member =
  | Spine_arg of lf_expr
  | Spine_car
  | Spine_cdr

let rec spine_member_list_to_spine = function
  | Spine_arg x :: a -> ARG(x,spine_member_list_to_spine a)
  | Spine_car :: a -> CAR(spine_member_list_to_spine a)
  | Spine_cdr :: a -> CDR(spine_member_list_to_spine a)
  | [] -> END

let rec exists_in_spine p args =
  match args with
  | ARG(x,a) -> p x || exists_in_spine p a
  | CAR a | CDR a -> exists_in_spine p a
  | END -> false

let rec args_length = function
  | CAR a | CDR a | ARG(_,a) -> 1 + args_length a
  | END -> 0

let args_fold f pi1 pi2 accu args = (* it's fold_left, which is the only direction that makes sense *)
  let rec repeat accu args =
    match args with
    | ARG(a,args) -> repeat (f accu a) args
    | CAR args -> repeat (pi1 accu) args
    | CDR args -> repeat (pi2 accu) args
    | END -> accu
  in repeat accu args

let args_iter f pi1 pi2 args =
  let rec repeat args =
    match args with
    | ARG(a,args) -> f a; repeat args
    | CAR args -> pi1 (); repeat args
    | CDR args -> pi2 (); repeat args
    | END -> ()
  in repeat args

let pi1 = function
  | pos, APPLY(h,args) -> (pos,APPLY(h,join_args args (CAR END)))
  | pos, CONS(x,_) -> x
  | _ -> (trap(); raise Internal)

let pi2 = function
  | pos, APPLY(h,args) -> (pos,APPLY(h,join_args args (CDR END)))
  | pos, CONS(_,y) -> y
  | _ -> (trap(); raise Internal)

(** Helper functions for making new ts-expressions from old ts-expressions. *)

let lambda1 v x = nowhere 55 (LAMBDA(v, x))
let lambda2 v1 v2 x = lambda1 v1 (lambda1 v2 x)
let lambda3 v1 v2 v3 x = lambda1 v1 (lambda2 v2 v3 x)

let make_Var c = Var c

let make_U h a = APPLY(U h, a)
let make_T h a = APPLY(T h, a)
let make_O h a = APPLY(O h, a)

let make_U_next x = make_U U_next (x ** END)
let make_U_max x y = make_U U_max (x **  y ** END)
let make_T_El x = make_T T_El (x ** END)
let make_T_U x = make_T T_U ( x ** END)
let make_T_Pi    t1 (x,t2) = make_T T_Pi    (t1 ** lambda1 x t2 ** END)
let make_T_Sigma t1 (x,t2) = make_T T_Sigma (t1 ** lambda1 x t2 ** END)
let make_T_Pt = make_T T_Pt END
let make_T_Coprod t t' = make_T T_Coprod (t ** t' ** END)
let make_T_Coprod2 t t' (x,u) (x',u') o = make_T T_Coprod2 (t ** t'** lambda1 x u ** lambda1 x' (u')** o ** END)
let make_T_Empty = make_T T_Empty END
let make_T_IP tA a (x,tB,(y,tD,(z,q))) = make_T T_IP (tA ** a ** lambda1 x tB ** lambda2 x y tD ** lambda3 x y z q ** END)
let make_T_Id t x y = make_T T_Id (t **x **y ** END)
let make_O_u m = make_O O_u (m ** END)
let make_O_j m n = make_O O_j (m ** n ** END)
let make_O_ev f p (v,t) = make_O O_ev (f **p **lambda1 v t ** END)
let make_O_lambda t (v,p) = make_O O_lambda (t ** lambda1 v p ** END)
let make_O_forall m m' n (v,o') = make_O O_forall (m **m'**n **lambda1 v (o') ** END)
let make_O_pair a b (x,t) = make_O O_pair (a **b **lambda1 x t ** END)
let make_O_pr1 t (x,t') o = make_O O_pr1 (t **lambda1 x (t')** o ** END)
let make_O_pr2 t (x,t') o = make_O O_pr2 (t **lambda1 x (t')** o ** END)
let make_O_total m1 m2 o1 (x,o2) = make_O O_total (m1 **m2 **o1 **lambda1 x o2 ** END)
let make_O_pt = make_O O_pt END
let make_O_pt_r o (x,t) = make_O O_pt_r (o **lambda1 x t ** END)
let make_O_tt = make_O O_tt END
let make_O_coprod m1 m2 o1 o2 = make_O O_coprod (m1 ** m2 ** o1 ** o2 ** END)
let make_O_ii1 t t' o = make_O O_ii1 (t **t'**o ** END)
let make_O_ii2 t t' o = make_O O_ii2 (t **t'**o ** END)
let make_O_sum tT tT' s s' o (x,tS) = make_O O_sum (tT ** tT'** s ** s'** o ** lambda1 x tS ** END)
let make_O_empty = make_O O_empty END
let make_O_empty_r t o = make_O O_empty_r (t ** o ** END)
let make_O_c tA a (x,tB,(y,tD,(z,q))) b f = make_O O_c ( 
  a ** lambda1 x tB ** lambda2 x y tD ** lambda3 x y z q  ** END)
let make_O_ip_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_O O_ip_r (
  tA ** a ** lambda1 x tB ** lambda2 x y tD ** lambda3 x y z q ** i ** lambda2  x' v tS ** t ** END)
let make_O_ip m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_O O_ip (
  m1 ** m2 ** m3 ** oA ** a ** lambda1 x oB ** lambda2 x y oD ** lambda3 x y z q  ** END)
let make_O_paths m t x y = make_O O_paths (m ** t ** x ** y ** END)
let make_O_refl t o = make_O O_refl (t ** o ** END)
let make_O_J tT a b q i (x,(e,tS)) = make_O O_J (tT ** a ** b ** q ** i ** lambda2 x e tS ** END)
let make_O_rr0 m2 m1 s t e = make_O O_rr0 (m2 ** m1 ** s ** t ** e ** END)
let make_O_rr1 m a p = make_O O_rr1 (m ** a ** p ** END)

(* 
  Local Variables:
  compile-command: "make -C .. src/helpers.cmo "
  End:
 *)
