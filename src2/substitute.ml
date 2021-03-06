(** Substitution. *)

open Expressions
open Relative
open Error

(** Routines for replacing relative variables (deBruijn index variables) by
    expressions.

    In these routines, [subs] is an array of expressions, whose i-th element is
    to replace [Rel (i + shift)] in [e], with its variables' relative
    indices increased by [shift].  Variables with relative indices too large to
    be covered have their indices decreased by the length of [subs].

    Descending into an expression with a bound variable increases [shift] by 1.

 *)

let rec join_args a b =
  if b = END then a else
  match a with
  | ARG(i,x,a) -> ARG(i,x,join_args a b)
  | END -> b

let apply_args e args =
  match e with
  | BASIC(h,brgs) -> BASIC(h, join_args brgs args)

let rec subst_expr shift subs e =
  match e with
  | BASIC(h,args) -> (
      let rec repeat shift args =
	match args with
	| ARG(i,x,a) ->
	    let shift = shift + i in
	    let x' = subst_expr shift subs x in
	    let a' = repeat shift a in
	    if x' == x && a' == a then args else ARG(i,x',a')
	| END -> args in
      let args' = repeat shift args in
      match h with
      | Var (Rel j) ->
	  if j < shift then e 
	  else
	    let i = j-shift in
	    if i < Array.length subs 
	    then apply_args (rel_shift_expr shift subs.(i)) args'
	    else BASIC(Var (Rel (j - Array.length subs)),args')
      | _ -> 
	  if args' == args then e else BASIC(h,args'))

and subst_expr_list shift subs s =
  match s with
  | x :: t ->
      let x' = subst_expr shift subs x in
      let t' = subst_expr_list shift subs t in
      if x == x' && t == t' then s else x' :: t'
  | [] -> []

and subst_jgmt shift subs j =
  match j with
  | J_Pi(a,b) ->
      let a' = subst_jgmt shift subs a in
      let shift = shift + 1 in
      let b' = subst_jgmt shift subs b in
      if a' == a && b' == b then j else J_Pi(a',b')
  | J_Basic(h,s) ->
      let s' = subst_expr_list shift subs s in
      if s == s' then j else J_Basic(h,s')

let subst_expr_l subs e = if Array.length subs = 0 then e else subst_expr 0 subs e

let subst_jgmt_l subs t = if Array.length subs = 0 then t else subst_jgmt 0 subs t

let preface subber x e = subber 0 [|x|] e

let subst_expr = preface subst_expr

let subst_jgmt = preface subst_jgmt

(*
  Local Variables:
  compile-command: "make -C .. src2/substitute.cmo "
  End:
 *)
