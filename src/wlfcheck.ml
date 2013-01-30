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

let uuu = nowhere 187 (APPLY(T T_U', END))

let rec check_istype env t =
  if not (List.exists (fun (v,u) -> equivalence t u) env.ts_context)
  then 
    match unmark t with
    | APPLY(T th, args) -> (
	match th with
	| T_Pi -> 
	    let (t1,t2) = args2 args in
	    check_istype env t1;
	    let w = newfresh (Var "t") in
	    let env = ts_bind env w t1 in
	    let w = var_to_lf w in
	    let t2 = Substitute.apply_args t2 (w ** END) in
	    check_istype env t2
	| T_U' -> ()
	| T_El' ->
	    let (o,p) = args2 args in
	    check_hastype env p o uuu
	| _ -> Lfcheck.err env (get_pos t) "invalid type, or not implemented yet")
    | _ -> Lfcheck.err env (get_pos t) "invalid type, or not implemented yet"

and check_hastype env p o t =
  if false then printf "check_hastype\n p = %a\n o = %a\n t = %a\n%!" _e p _e o _e t;
  match unmark p with
  | APPLY(V (Var_wd i), END) -> (
      let (v,u) =
	try
	  ts_fetch_from_top env i 
	with
	  Invalid_argument _ -> Lfcheck.err env (get_pos p) ("non-existent context position " ^ string_of_int i)
      in
      if false then printf " v = %a\n u = %a\n%!" _v v _e u;
      if not (compare_var_to_expr v o) then Lfcheck.err env (get_pos o) ("expected variable " ^ vartostring v);
      if not (equality t u) then Lfcheck.mismatch_term env (get_pos t) t (get_pos u) u)
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_wev -> ( 
	  let (pf,po) = args2 pargs in
	  match unmark o with
	  | APPLY(O O_ev,args) ->
	      let (f,o,t1,t2) = args4 args in
	      check_hastype env po o t1;
	      let u = nowhere 123 (APPLY(T T_Pi,t1 ** t2 ** END)) in
	      check_hastype env pf f u;
	      let t2' = Substitute.subst_expr (Var_wd env.ts_context_length, po) (Substitute.apply_args t2 (o ** END)) in
	      if not (equivalence t2' t) then Lfcheck.mismatch_term env (get_pos t2') t2' (get_pos t) t;
	  | _ -> raise FalseWitness)
      | W_wlam -> 
	  let p = args1 pargs in (
	  match unmark o with
	  | APPLY(O O_lambda,args) ->
	      let (t1',o) = args2 args in (
	      match unmark t with
	      | APPLY(T T_Pi, ARG(t1,ARG(t2,END))) -> (
		  if not (equivalence t1' t1) then Lfcheck.mismatch_term env (get_pos t) t (get_pos t1) t1;
		  let v = newfresh (Var "x") in
		  let env = ts_bind env v t1 in
		  let v = var_to_lf v ** END in 
		  let p = Substitute.apply_args p v in
		  let o = Substitute.apply_args o v in
		  let t2 = Substitute.apply_args t2 v in
		  check_hastype env p o t2)
	      | _ -> Lfcheck.err env (get_pos t) "expected a function type")
	  | _ -> Lfcheck.err env (get_pos o) "expected a function")
      | W_wconv -> raise NotImplemented
      | W_wconveq -> raise NotImplemented
      | W_weleq -> raise NotImplemented
      | W_wpi1 -> raise NotImplemented
      | W_wpi2 -> raise NotImplemented
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
  | _ -> Lfcheck.err env (get_pos p) ("expected a witness expression: " ^ lf_expr_to_string p)

and check_type_equality env p t t' =
  raise NotImplemented

and check_object_equality env p o o' t =
  raise NotImplemented

let check (env:context) (t:lf_type) =
  (* try *)
    match unmark t with 
    | F_Apply(F_istype,[t]) -> check_istype env t
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
