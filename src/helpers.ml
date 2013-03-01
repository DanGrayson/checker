(** Helper functions for dealing with expressions. *)

open Error
open Variables
open Typesystem
open Names

let isunused_variable_expression x =
  match unmark x with
  | APPLY(V v, END) -> isunused v
  | _ -> false

exception Args_match_failure

let args1 s =
  match s with
  | ARG(x,END) -> x
  | _ -> raise Args_match_failure

let args2 s =
  match s with
  | ARG(x,ARG(y,END)) -> x,y
  | _ -> raise Args_match_failure

let args3 s =
  match s with
  | ARG(x,ARG(y,ARG(z,END))) -> x,y,z
  | _ -> raise Args_match_failure

let args4 s =
  match s with
  | ARG(x,ARG(y,ARG(z,ARG(a,END)))) -> x,y,z,a
  | _ -> raise Args_match_failure

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

let map_spine f args =
  let rec repeat s = match s with
  | ARG(x,a) -> let x' = f x in let a' = repeat a in if x' == x && a' == a then s else ARG(x',a')
  | CAR a -> let a' = repeat a in if a' == a then s else CAR(a')
  | CDR a -> let a' = repeat a in if a' == a then s else CDR(a')
  | END -> s
  in repeat args

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

let locate x l =
    let rec repeat i = function
    | a :: l -> if compare a x == 0 then i else repeat (i+1) l
    | [] -> raise Not_found
    in repeat 0 l

(** Routines for replacing named variables by relative index variables in expressions. *)
let rec var_subst_expr shift subl e =
  match unmark e with
  | APPLY(h,args) -> (
      let args' = map_spine (var_subst_expr shift subl) args in
      match h with
      | V ((Var _ | Var_wd _) as v) -> (
	  try
	    get_pos e, APPLY(V (VarRel (locate v subl + shift)),args')
	  with Not_found ->
	    if args == args' then e else get_pos e, APPLY(h,args'))
      | W _ | V _ | U _ | T _ | O _ | TAC _ ->
	  if args == args' then e else get_pos e, APPLY(h,args'))
  | CONS(x,y) ->
      let x' = var_subst_expr shift subl x in
      let y' = var_subst_expr shift subl y in
      if x' == x && y' == y then e else get_pos e, CONS(x',y')
  | LAMBDA(v, body) ->
      let shift = shift + 1 in
      let body' = var_subst_expr shift subl body in
      if body' == body then e else get_pos e, LAMBDA(v, body')

and var_subst_type shift subl t =
  match unmark t with
  | F_Pi(v,a,b) ->
      let a' = var_subst_type shift subl a in
      let shift = shift + 1 in
      let b' = var_subst_type shift subl b in
      if a' == a && b' == b then t else get_pos t, F_Pi(v,a',b')
  | F_Sigma(v,a,b) ->
      let a' = var_subst_type shift subl a in
      let shift = shift + 1 in
      let b' = var_subst_type shift subl b in
      if a' == a && b' == b then t else get_pos t, F_Sigma(v,a',b')
  | F_Apply(label,args) ->
      let args' = List.map (var_subst_expr shift subl) args in
      if args' == args then t else get_pos t, F_Apply(label, args')
  | F_Singleton(e,u) ->
      let e' = var_subst_expr shift subl e in
      let u' = var_subst_type shift subl u in
      if e' == e && u' == u then t else get_pos t, F_Singleton(e',u')

let rec var_subst_kind shift subl k =
   match k with
   | K_primitive_judgment | K_ulevel | K_expression | K_judgment | K_witnessed_judgment | K_judged_expression -> k
   | K_Pi(v,a,b) ->
       let a' = var_subst_type shift subl a in
       let shift = shift + 1 in
       let b' = var_subst_kind shift subl b in
       if a' == a && b' == b then k else K_Pi(v, a, b)

let var_subst_expr subl e = var_subst_expr 0 subl e

let var_subst_type subl t = var_subst_type 0 subl t

let var_subst_kind subl t = var_subst_kind 0 subl t

(** Helper functions for making new ts-expressions from old ts-expressions. *)

let rel1_expr v0 x = var_subst_expr [v0] x

let rel2_expr v0 v1 x = var_subst_expr [v0;v1] x

let rel3_expr v0 v1 v2 x = var_subst_expr [v0;v1;v2] x

let rel1_type v0 t = var_subst_type [v0] t

let rel2_type v0 v1 t = var_subst_type [v0;v1] t

let rel3_type v0 v1 v2 t = var_subst_type [v0;v1;v2] t

let abstract_expr v x = v, rel1_expr v x

let abstract_type v x = v, rel1_type v x

let lambda1 v0 x =
  with_pos_of x (
  LAMBDA(v0, rel1_expr v0 x))

let lambda2 v0 v1 x =
  with_pos_of x (
  LAMBDA(v0,
	 with_pos_of x (
	 LAMBDA(v1, rel2_expr v0 v1 x))))

let lambda3 v0 v1 v2 x =
  with_pos_of x (
  LAMBDA(v0,
	 with_pos_of x (
	 LAMBDA(v1,
		with_pos_of x (
		LAMBDA(v2,
		       rel3_expr v0 v1 v2 x))))))

let make_Var c = Var c

let make_F_Pi t (v,u) = F_Pi(v, t, rel1_type v u)
let make_F_Pi_simple t u = F_Pi(Var "_", t, u)
let make_F_Sigma t (v,u) = F_Sigma(v, t, rel1_type v u)
let make_F_Sigma_simple t u = F_Sigma(Var "_", t, u)

let make_U h a = APPLY(U h, a)
let make_T h a = APPLY(T h, a)
let make_O h a = APPLY(O h, a)
let make_W h a = APPLY(W h, a)

let make_U_next x = make_U U_next (x ** END)
let make_U_max x y = make_U U_max (x **  y ** END)

let uuu = nowhere 187 (APPLY(T T_U', END))

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

let make_W_wev p q = make_W W_wev (p ** q ** END)
let make_W_wbeta p q = make_W W_wbeta (p ** q ** END)
let make_W_wlam p = make_W W_wlam (p ** END)
let make_W_wrefl p p' = make_W W_wrefl (p ** p' ** END)
let make_W_weleq peq = make_W W_weleq (peq ** END)
let make_W_Wrefl = make_W W_wrefl END
let make_T_Pi' t1 t2 = make_T T_Pi' (t1 ** t2 ** END)

let this_object_of_type pos o t =
  let v = Var "x" in
  let a = with_pos pos (F_Singleton(o,oexp)) in
  let b = hastype (nowhere 126 (APPLY(V v,END))) t in
  with_pos pos (make_F_Sigma a (v,b))

(*
  Local Variables:
  compile-command: "make -C .. src/helpers.cmo "
  End:
 *)
