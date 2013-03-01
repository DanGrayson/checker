(** Substitution. *)

open Error
open Variables
open Typesystem
open Helpers
open Names
open Printer
open Printf

(** Routines for replacing relative variables (deBruijn index variables) by expressions.

    Coming soon ...
 *)

(** Routines for replacing named variables by expressions. *)

let show_subs (subl : (var * lf_expr) list) =
  printf " subs =\n";
  List.iter (fun (v,e) -> printf "   %a => %a\n" _v v _e e) subl

let rec subst_expr subl e =
  let pos = get_pos e in
  match unmark e with
  | APPLY(h,args) -> (
      let args = map_spine (subst_expr subl) args in
      match h with
      | V v -> (
	  try apply_args (new_pos pos (List.assoc v subl)) args
	  with Not_found -> pos, APPLY(h,args))
      | W _ | U _ | T _ | O _ | TAC _ -> pos, APPLY(h,args))
  | CONS(x,y) -> pos, CONS(subst_expr subl x,subst_expr subl y)
  | LAMBDA(v, body) ->
      let body' = subst_expr subl body in
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
        | ARG(x,args) -> repeat (subst_expr [(v,x)] body) args
        | CAR args -> raise (GeneralError "pi1 expected a pair (1)")
	| CDR args -> raise (GeneralError "pi2 expected a pair (1)")
        | END -> e)
  in repeat e args

and subst_type_list (subl : (var * lf_expr) list) ts = List.map (subst_type subl) ts

and subst_type (subl : (var * lf_expr) list) (pos,t) =
  (pos,
   match t with
   | F_Pi(v,a,b) ->
       let a = subst_type subl a in
       let b = subst_type subl b in
       F_Pi(v,a,b)
   | F_Sigma(v,a,b) ->
       let a = subst_type subl a in
       let b = subst_type subl b in
       F_Sigma(v,a,b)
   | F_Apply(label,args) -> F_Apply(label, List.map (subst_expr subl) args)
   | F_Singleton(e,t) -> F_Singleton( subst_expr subl e, subst_type subl t )
  )

let rec subst_kind subl k =
   match k with
   | K_primitive_judgment | K_ulevel | K_expression | K_judgment | K_witnessed_judgment | K_judged_expression -> k
   | K_Pi(v,a,b) ->
       let a = subst_type subl a in
       let b = subst_kind subl b in
       K_Pi(v, a, b)

let subst_l subs e = if subs = [] then e else subst_expr subs e

let subst_type_l subs t = if subs = [] then t else subst_type subs t

let preface subber (v,x) e = subber [(v,x)] e

let subst_expr = preface subst_expr

let subst_type = preface subst_type

let subst_kind = preface subst_kind

(*
  Local Variables:
  compile-command: "make -C .. src/substitute.cmo "
  End:
 *)
