(** Check witnessed judgments for correctness. *)

open Variables
open Typesystem
open Printer
open Printf
open Error
open Helpers

exception FalseWitness

let equality = Alpha.UEqual.term_equiv empty_uContext
    (* Here equality is alpha-equivalence *)

let equivalence = equality
    (* We still have to implement the relation called ~ in the paper, which ignores inessential subterms. *)
    (* For now we use equality. *)

let compare_var_to_expr v e =
  match unmark e with
  | APPLY(V w, END) -> v = w
  | _ -> false

let rec check_hastype env p o t =
  if false then printf "check_hastype\n p = %a\n o = %a\n t = %a\n%!" _e p _e o _e t;
  match unmark p with
  | APPLY(V (Var_wd i), END) ->
      let (v,u) = ts_fetch_from_top env i in
      if false then printf " v = %a\n u = %a\n%!" _v v _e u;
      if not (compare_var_to_expr v o) then Lfcheck.err env (get_pos o) ("expected variable " ^ vartostring v);
      if not (equality t u) then Lfcheck.mismatch_term env (get_pos t) t (get_pos u) u      
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_wev -> ( 
	  let (pf,po) = args2 pargs in
	  match unmark o with
	  | APPLY(O O_ev',args) ->
	      let (f,o,t1,t2) = args4 args in
	      check_hastype env po o t1;
	      (* check_hastype env pf f (...); *)
	      raise NotImplemented
	  | _ -> raise FalseWitness)
      | W_wconv -> raise NotImplemented
      | W_wconveq -> raise NotImplemented
      | W_weleq -> raise NotImplemented
      | W_wpi1 -> raise NotImplemented
      | W_wpi2 -> raise NotImplemented
      | W_wlam -> raise NotImplemented
      | W_wl1 -> raise NotImplemented
      | W_wl2 -> raise NotImplemented
      | W_wevt1 -> raise NotImplemented
      | W_wevt2 -> raise NotImplemented
      | W_wevf -> raise NotImplemented
      | W_wevo -> raise NotImplemented
      | W_wbeta -> raise NotImplemented
      | W_weta -> raise NotImplemented
      | W_Wsymm
      | W_Wtrans
      | W_wrefl
      | W_wsymm
      | W_wtrans
      | W_Wrefl -> raise FalseWitness
     )
  | _ -> raise FalseWitness

and check_type_equality env p t t' =
  raise NotImplemented

and check_object_equality env p o o' t =
  raise NotImplemented

let check (env:context) (t:lf_type) =
  (* try *)
    match unmark t with 
    | F_Apply(F_witnessed_hastype,[p;o;t]) -> check_hastype env p o t
    | F_Apply(F_witnessed_type_equality,[p;t;t']) -> check_type_equality env p t t'
    | F_Apply(F_witnessed_object_equality,[p;o;o';t]) -> check_object_equality env p o o' t
    | _ -> Lfcheck.err env (get_pos t) "expected a witnessed judgment"
  (* with *)
  (*   FalseWitness -> Lfcheck.err env (get_pos t) "incorrect witness" *)

(* 
  Local Variables:
  compile-command: "make -C .. src/wlfcheck.cmo "
  End:
 *)
