(** Substitution. *)

open Typesystem
open Helpers
open Names
open Printer
open Printf
open Error

(** Routines for replacing relative variables (deBruijn index variables) by
    expressions.

    In these routines, [subs] is an array of expressions, whose i-th element is
    to replace [Rel (i + shift)] in [e], with its variables' relative
    indices increased by [shift].  Variables with relative indices too large to
    be covered have their indices decreased by the length of [subs].

    Descending into an expression with a bound variable increases [shift] by 1.

 *)

let apply_args_counter = Error.new_counter()

let rec subst_expr shift subs e =
  if debug_subst then printf "subst_expr shift=%d subs=%a e=%a\n%!" shift _a (empty_environment,subs) _e (empty_environment,e);
  let pos = get_pos e in
  match unmark e with
  | BASIC(h,args) -> (
      let args' = map_expr_list (subst_expr shift subs) args in
      match h with
      | V (Rel j) ->
	  if j < shift then e 
	  else
	    let i = j-shift in
	    if i < Array.length subs 
	    then apply_args (rel_shift_expr shift subs.(i)) args'
	    else pos, BASIC(V (Rel (j - Array.length subs)),args')
      | _ -> 
	  if args' == args then e else pos, BASIC(h,args'))
  | PAIR(x,y) -> 
      let x' = subst_expr shift subs x
      and y' = subst_expr shift subs y in
      if x' == x && y' == y then e else pos, PAIR(x',y')
  | TEMPLATE(v, body) ->
      let shift = shift + 1 in
      let body' = subst_expr shift subs body in
      if body' == body then e else pos, TEMPLATE(v, body')

and apply_args e args =
  let c = apply_args_counter() in
  if debug_subst then printf "entering apply_args(%d): e = %a, args = %a\n%!" c _e (empty_environment,e) _s args;
  let r =
  let pos = get_pos e in
  match unmark e with
  | BASIC(h,brgs) -> (pos, BASIC(h, join_args brgs args))
  | PAIR(x,y) -> (
      match args with
      | ARG _ -> raise (GeneralError "application of a pair to an argument")
      | FST args -> apply_args x args
      | SND args -> apply_args y args
      | END -> e)
  | TEMPLATE(_,body) -> (
      match args with
      | ARG(x,args) -> 
	  apply_args (subst_expr 0 [|x|] body) args
      | FST args -> raise (GeneralError "pi1 expected a pair but got a function")
      | SND args -> raise (GeneralError "pi2 expected a pair but got a function")
      | END -> e)
  in
  if debug_subst then printf "leaving apply_args(%d): r = %a\n%!" c _e (empty_environment,r);
  r

and subst_type shift subs t =
  if debug_subst then printf "subst_type shift=%d subs=%a t=%a\n%!" shift _a (empty_environment,subs) _t (empty_environment,t);
  match unmark t with
  | J_Pi(v,a,b) ->
      let a' = subst_type shift subs a in
      let shift = shift + 1 in
      let b' = subst_type shift subs b in
      if a' == a && b' == b then t else get_pos t, J_Pi(v,a',b')
  | J_Sigma(v,a,b) ->
      let a' = subst_type shift subs a in
      let shift = shift + 1 in
      let b' = subst_type shift subs b in
      if a' == a && b' == b then t else get_pos t, J_Sigma(v,a',b')
  | J_Singleton(e,u) ->
      let e' = subst_expr shift subs e in
      let u' = subst_type shift subs u in
      if e' == e && u' == u then t else get_pos t, J_Singleton(e',u')
  | J_Basic(label,args) -> 
      let args' = map_list (subst_expr shift subs) args in
      if args' == args then t else get_pos t, J_Basic(label, args')

let rec subst_kind shift subs k =
   match k with
   | K_basic_judgment | K_ulevel | K_syntactic_judgment | K_derived_judgment | K_witnessed_judgment -> k
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
