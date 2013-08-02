(** Expressions *) (* -*- coding: utf-8 -*- *)

type var =
  | Rel of int			(* deBruijn index, starting with 0 *)

let vartostring = function
  | Rel i -> string_of_int i ^ "^"	(* raw form *)

type uHead = | U_next | U_max
type tHead = | T_El | T_U | T_Pi | T_Sigma | T_Pt
             | T_Coprod | T_Coprod2 | T_Empty | T_IP | T_Id
type oHead = | O_u | O_j | O_ev | O_lambda | O_forall | O_pair | O_pr1
	     | O_pr2 | O_total | O_pt | O_pt_r | O_tt | O_coprod | O_ii1 | O_ii2 | O_sum
	     | O_empty | O_empty_r | O_c | O_ip_r | O_ip | O_paths | O_refl | O_J | O_rr0
	     | O_rr1 | O_nat | O_nat_r | O_O | O_S
type wHead = | W_Wrefl | W_Wsymm | W_Wtrans | W_wrefl | W_wsymm | W_wtrans | W_wconv
	     | W_wconveq | W_weleq | W_wpi1 | W_wpi2 | W_wlam | W_wl1 | W_wl2 | W_wev
	     | W_wevt1 | W_wevt2 | W_wevf | W_wevo | W_wbeta | W_weta

type expr_head = | U of uHead | T of tHead | O of oHead | W of wHead | V of var

type expr =
  | BASIC of expr_head * expr_list
and expr_list =
  | ARG of int * expr * expr_list	(* the integer gives the number of variables bound in expr *)
  | END

type judgment = 
    (* 
       If the last expr is missing, then it represents a hypothesis.  We may want
       to factor it out.  
     *)
  | J_istype of expr option			           (* t represents |- t type *)
  | J_hastype of expr * expr option		           (* (t,o) represents |- o : t *)
  | J_type_equality of expr * expr * expr option	   (* (t,t',p) represents |- p : t = t' *)
  | J_object_equality of expr * expr * expr * expr option  (* (t, o, o',p) represents |- p : o = o' : t *)
  | J_Pi of judgment * judgment				   (* 
							      (j,k) represents the judgment that j entails k 
							      Here j should have the last expr missing, and
							      the corresponding variable is bound in k.
							    *)

(** Functions *)

let var_to_expr v = BASIC(V v,END)

let rec rel_shift_expr limit shift e =
  if shift = 0 then e else
  match e with
  | BASIC(h,args) ->
      let rec repeat s = match s with
      | ARG(i,x,a) -> 
	  let limit = limit + i in
	  let x' = rel_shift_expr limit shift x in
	  let a' = repeat a in
	  if x' == x && a' == a then s else ARG(i,x',a')
      | END -> s
      in
      let args' = repeat args in
      let h' = rel_shift_head limit shift h in
      if h' == h && args' == args then e else BASIC(h',args')

and rel_shift_head limit shift h = 
  match h with
  | V (Rel i) when i >= limit -> V (Rel (shift+i))
  | _ -> h

and rel_shift_jgmt limit shift j =
  match j with
  | J_Pi(a,b) ->
      let a' = rel_shift_jgmt limit shift a in
      let limit = limit + 1 in
      let b' = rel_shift_jgmt limit shift b in
      if a' == a && b' == b then j else J_Pi(a',b')
  | J_istype(None) -> j
  | J_istype(Some t) ->
      let t' = rel_shift_expr limit shift t in
      if t == t' then j else J_istype(Some t')
  | J_hastype(t,None) ->
      let t' = rel_shift_expr limit shift t in
      if t == t' then j else J_hastype(t',None)
  | J_hastype(t,Some o) ->
      let t' = rel_shift_expr limit shift t in
      let o' = rel_shift_expr limit shift o in
      if t == t' && o == o' then j else J_hastype(t',Some o')
  | J_type_equality(t,u,None) ->
      let t' = rel_shift_expr limit shift t in
      let u' = rel_shift_expr limit shift u in
      if t == t' && u == u' then j else J_type_equality(t',u',None)
  | J_type_equality(t,u,Some o) ->
      let t' = rel_shift_expr limit shift t in
      let u' = rel_shift_expr limit shift u in
      let o' = rel_shift_expr limit shift o in
      if t == t' && u == u' && o == o' then j else J_type_equality(t',u',Some o')
  | J_object_equality(t,n,o,None) ->
      let t' = rel_shift_expr limit shift t in
      let n' = rel_shift_expr limit shift n in
      let o' = rel_shift_expr limit shift o in
      if t == t' && n == n' && o == o' then j else J_object_equality(t',n',o',None)
  | J_object_equality(t,n,o,Some p) ->
      let t' = rel_shift_expr limit shift t in
      let n' = rel_shift_expr limit shift n in
      let o' = rel_shift_expr limit shift o in
      let p' = rel_shift_expr limit shift p in
      if t == t' && n == n' && o == o' && p == p' then j else J_object_equality(t',n',o',Some p')

let rel_shift_expr shift e = if shift = 0 then e else rel_shift_expr 0 shift e

let rel_shift_head shift h = if shift = 0 then h else rel_shift_head 0 shift h

let rel_shift_jgmt shift t = if shift = 0 then t else rel_shift_jgmt 0 shift t

(*
  Local Variables:
  compile-command: "make -C .. src/expressions.cmo "
  End:
 *)
