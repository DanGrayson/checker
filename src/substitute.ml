(** Substitution. *)

open Error
open Variables
open Typesystem
open Helpers
open Names
open Printer
open Printf

(** Routines for replacing relative variables (deBruijn index variables) by expressions.

    In these routines, [subs] is an array of expressions, whose i-th element is
    to replace (VarRel i), if i is small enough, otherwise i is decreased by the
    length of [subs].
 *)
let rec subst_expr shift subs e =
  let pos = get_pos e in
  match unmark e with
  | APPLY(h,args) -> (
      let args' = map_spine (subst_expr shift subs) args in
      match h with
      | V (VarRel i) ->
	  if i < shift then e else
	  if i-shift < Array.length subs 
	  then apply_args (rel_shift_expr shift subs.(i-shift)) args'
	  else pos, APPLY(V (VarRel (i - Array.length subs)),args')
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

and apply_args e args =
  let rec repeat e args =
    let pos = get_pos e in
    match unmark e with
    | APPLY(h,brgs) -> (pos, APPLY(h, join_args brgs args))
    | CONS(x,y) -> (
        match args with
        | ARG _ -> raise (GeneralError "too many arguments")
        | CAR args -> repeat x args
	| CDR args -> repeat y args
        | END -> e)
    | LAMBDA(v,body) -> (
        match args with
        | ARG(x,args) -> repeat (subst_expr 0 [|x|] body) args
        | CAR args -> raise (GeneralError "pi1 expected a pair (1)")
	| CDR args -> raise (GeneralError "pi2 expected a pair (1)")
        | END -> e)
  in repeat e args

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
  | F_Singleton(e,t) ->
      let e' = subst_expr shift subs e in
      let t' = subst_type shift subs t in
      if e' == e && t' == t then t else get_pos t, F_Singleton(e',t')
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
