(** Substitution. *)

open Error
open Variables
open Typesystem
open Helpers
open Names
open Printer
open Printf

(** Routines for replacing relative variables (deBruijn index variables) by
    expressions.

    In these routines, [subs] is an array of expressions, whose i-th element is
    to replace [VarRel (i + shift)] in [e], with its variables' relative
    indices increased by [shift].  Variables with relative indices too large to
    be covered have their indices decreased by the length of [subs].

    Descending into an expression with a bound variable increases [shift] by 1.

 *)
let rec subst_expr shift subs e =
  let pos = get_pos e in
  match unmark e with
  | APPLY(h,args) -> (
      let args' = map_spine (subst_expr shift subs) args in
      match h with
      | V (VarRel j) ->
	  if j < shift then e 
	  else
	    let i = j-shift in
	    if i < Array.length subs 
	    then apply_args (rel_shift_expr shift subs.(i)) args'
	    else pos, APPLY(V (VarRel (j - Array.length subs)),args')
      | _ -> 
	  if args' == args then e else pos, APPLY(h,args'))
  | CONS(x,y) -> 
      let x' = subst_expr shift subs x in
      let y' = subst_expr shift subs y in
      if x' == x && y' == y then e else pos, CONS(x',y')
  | LAMBDA(v, body) ->
      let shift = shift + 1 in
      let body' = subst_expr shift subs body in
      if body' == body then e else pos, LAMBDA(v, body')

and apply_args shift e args =
  let rec repeat shift e args =
    let pos = get_pos e in
    match unmark e with
    | APPLY(h,brgs) -> (pos, APPLY(h, join_args brgs args))
    | CONS(x,y) -> (
        match args with
        | ARG _ -> raise (GeneralError "too many arguments")
        | CAR args -> repeat shift x args
	| CDR args -> repeat shift y args
        | END -> e)
    | LAMBDA(v,body) -> (
        match args with
        | ARG(x,args) -> repeat shift (subst_expr 0 [|x|] body) args
        | CAR args -> raise (GeneralError "pi1 expected a pair")
	| CDR args -> raise (GeneralError "pi2 expected a pair")
        | END -> e)
  in repeat shift e args

and subst_type shift subs t =
  match unmark t with
  | F_Pi(v,a,b) ->
      let a' = subst_type shift subs a in
      let shift = shift + 1 in
      let b' = subst_type shift subs b in
      if a' == a && b' == b then t else get_pos t, F_Pi(v,a',b')
  | F_Sigma(v,a,b) ->
      let a' = subst_type shift subs a in
      let shift = shift + 1 in
      let b' = subst_type shift subs b in
      if a' == a && b' == b then t else get_pos t, F_Sigma(v,a',b')
  | F_Singleton(e,u) ->
      let e' = subst_expr shift subs e in
      let u' = subst_type shift subs u in
      if e' == e && u' == u then t else get_pos t, F_Singleton(e',u')
  | F_Apply(label,args) -> 
      let args' = map_list (subst_expr shift subs) args in
      if args' == args then t else get_pos t, F_Apply(label, args')

let rec subst_kind shift subs k =
   match k with
   | K_primitive_judgment | K_ulevel | K_expression | K_judgment | K_witnessed_judgment | K_judged_expression -> k
   | K_Pi(v,a,b) ->
       let a' = subst_type shift subs a in
       let shift = shift + 1 in
       let b' = subst_kind shift subs b in
       if a' == a && b' == b then k else K_Pi(v,a',b')

let subst_l subs e = if Array.length subs = 0 then e else subst_expr 0 subs e

let subst_type_l subs t = if Array.length subs = 0 then t else subst_type 0 subs t

let preface subber x e = subber 0 [|x|] e

let subst_expr = preface subst_expr

let subst_type = preface subst_type

let subst_kind = preface subst_kind

(*
  Local Variables:
  compile-command: "make -C .. src/substitute.cmo "
  End:
 *)
