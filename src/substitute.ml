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

let show_subs (subs : lf_expr array) =
  printf " subs =\n";
  Array.iteri (fun i e -> printf "   %a => %a\n" _v (VarRel i) _e e) subs

let rec subst_expr subs e =
  let pos = get_pos e in
  match unmark e with
  | APPLY(h,args) -> (
      let args = map_spine (subst_expr subs) args in
      match h with
      | V (VarRel i) ->
	  if i < Array.length subs 
	  then apply_args (new_pos pos subs.(i)) args
	  else pos, APPLY(V (VarRel (i - Array.length subs)),args)
      | _ -> pos, APPLY(h,args))
  | CONS(x,y) -> pos, CONS(subst_expr subs x,subst_expr subs y)
  | LAMBDA(v, body) ->
      let body' = subst_expr subs body in
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
        | ARG(x,args) -> repeat (subst_expr [|x|] body) args
        | CAR args -> raise (GeneralError "pi1 expected a pair (1)")
	| CDR args -> raise (GeneralError "pi2 expected a pair (1)")
        | END -> e)
  in repeat e args

and subst_type_list subs ts = List.map (subst_type subs) ts

and subst_type subs (pos,t) =
  (pos,
   match t with
   | F_Pi(v,a,b) ->
       let a = subst_type subs a in
       let b = subst_type subs b in
       F_Pi(v,a,b)
   | F_Sigma(v,a,b) ->
       let a = subst_type subs a in
       let b = subst_type subs b in
       F_Sigma(v,a,b)
   | F_Apply(label,args) -> F_Apply(label, List.map (subst_expr subs) args)
   | F_Singleton(e,t) -> F_Singleton( subst_expr subs e, subst_type subs t )
  )

let rec subst_kind subs k =
   match k with
   | K_primitive_judgment | K_ulevel | K_expression | K_judgment | K_witnessed_judgment | K_judged_expression -> k
   | K_Pi(v,a,b) ->
       let a = subst_type subs a in
       let b = subst_kind subs b in
       K_Pi(v, a, b)

let subst_l subs e = if Array.length subs = 0 then e else subst_expr subs e

let subst_type_l subs t = if Array.length subs = 0 then t else subst_type subs t

let preface subber x e = subber [|x|] e

let subst_expr = preface subst_expr

let subst_type = preface subst_type

let subst_kind = preface subst_kind

(*
  Local Variables:
  compile-command: "make -C .. src/substitute.cmo "
  End:
 *)
