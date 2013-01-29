(** Check witnessed judgments for correctness. *)

open Variables
open Typesystem
open Printer
open Printf
open Error

let alpha = Alpha.UEqual.term_equiv empty_uContext 

let compare_var_to_expr v e =
  match unmark e with
  | APPLY(V w, END) -> v = w
  | _ -> false

let check_hastype env p o t =
  if false then printf "check_hastype\n p = %a\n o = %a\n t = %a\n%!" _e p _e o _e t;
  match unmark p with
  | APPLY(V (Var_wd i), END) ->
      let (v,u) = ts_fetch_from_top env i in
      if false then printf " v = %a\n u = %a\n%!" _v v _e u;
      if not (compare_var_to_expr v o) then Lfcheck.err env (get_pos o) ("expected variable " ^ vartostring v);
      if not (alpha t u) then Lfcheck.mismatch_term env (get_pos t) t (get_pos u) u      
  | _ -> Lfcheck.err env (get_pos p) "incorrect witness"

let check_type_equality env p t t' =
  raise NotImplemented

let check_object_equality env p o o' t =
  raise NotImplemented

let check (env:context) (t:lf_type) =
  match unmark t with 
  | F_Apply(F_witnessed_hastype,[p;o;t]) -> check_hastype env p o t
  | F_Apply(F_witnessed_type_equality,[p;t;t']) -> check_type_equality env p t t'
  | F_Apply(F_witnessed_object_equality,[p;o;o';t]) -> check_object_equality env p o o' t
  | _ -> Lfcheck.err env (get_pos t) "expected a witnessed judgment"

(* 
  Local Variables:
  compile-command: "make -C .. src/wlfcheck.cmo "
  End:
 *)
