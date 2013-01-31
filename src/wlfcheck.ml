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

let open_context t1 (env,p,o,t2) =
  let v = newfresh (Var "x") in
  let v' = newfresh (Var_wd "x") in
  let env = tts_bind env v' v t1 in
  let e = var_to_lf v' ** var_to_lf v ** END in 
  let p = Substitute.apply_args p e in
  let o = Substitute.apply_args o e in
  let t2 = Substitute.apply_args t2 e in
  (env,p,o,t2)

let rec check_istype env t =
  if not (List.exists (fun (v,u) -> equivalence t u) env.ts_context)
  then 
    match unmark t with
    | APPLY(T th, args) -> (
	match th with
	| T_Pi' -> 
	    let (t1,t2) = args2 args in
	    check_istype env t1;
	    let p = newfresh (Var_wd "o") in
	    let o = newfresh (Var "o") in
	    let env = tts_bind env p o t1 in
	    let p = var_to_lf p in
	    let o = var_to_lf o in
	    let t2 = Substitute.apply_args t2 (p ** o ** END) in
	    check_istype env t2
	| T_U' -> ()
	| T_El' ->
	    let (p,o) = args2 args in
	    check_hastype env p o uuu
	| _ -> Lfcheck.err env (get_pos t) "invalid type, or not implemented yet.")
    | _ -> Lfcheck.err env (get_pos t) ("invalid type, or not implemented yet: " ^ ts_expr_to_string t)

and check_hastype env p o t =
  if false then printf "check_hastype\n p = %a\n o = %a\n t = %a\n%!" _e p _e o _e t;
  match unmark p with
  | APPLY(V (Var_wd _ | VarGen_wd _ as w), END) -> (
      let (o',t') = 
	try tts_fetch_w w env
	with Not_found -> Lfcheck.err env (get_pos p) "variable not in context" in
      if not (compare_var_to_expr o' o) then Lfcheck.err env (get_pos o) ("expected variable " ^ vartostring o');
      if not (equality t t') then Lfcheck.mismatch_term env (get_pos t) t (get_pos t') t')
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_wev -> ( 
	  let (pf,po) = args2 pargs in
	  match unmark o with
	  | APPLY(O O_ev',args) ->
              let (f,o,t1,t2) = args4 args in
              check_hastype env po o t1;
              let u = nowhere 123 (APPLY(T T_Pi', t1 ** t2 ** END)) in
              check_hastype env pf f u;
              let t2' = Substitute.apply_args t2 (po ** o ** END) in
              if not (equivalence t2' t) then Lfcheck.mismatch_term env (get_pos t2') t2' (get_pos t) t;
          | _ -> raise FalseWitness)
      | W_wlam -> 
	  let p = args1 pargs in (
	  match unmark o with
	  | APPLY(O O_lambda',args) ->
	      let (t1',o) = args2 args in (
	      match unmark t with
	      | APPLY(T T_Pi', ARG(t1,ARG(t2,END))) -> (
		  if not (equivalence t1' t1) then Lfcheck.mismatch_term env (get_pos t) t (get_pos t1) t1;
		  let (env,p,o,t2) = open_context t1 (env,p,o,t2) in
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
  match unmark p with
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_wbeta -> (
	  let (p1,p2) = args2 pargs in
	  match unmark o with 
	  | APPLY(O O_ev',args) ->
              let (f,o1,t1,t2) = args4 args in (
	      match unmark f with 
	      | APPLY(O O_lambda',fargs) ->
		  let (t1,o2) = args2 fargs in
		  check_hastype env p1 o1 t1;
		  let (env,p2',o2',t2') = open_context t1 (env,p2,o2,t2) in
		  check_hastype env p2' o2' t2';
		  let t2'' = Substitute.apply_args t2 (p1 ** o1 ** END) in
		  if not (equivalence t2'' t) then Lfcheck.mismatch_term env (get_pos t2'') t2'' (get_pos t) t;
		  let o2' = Substitute.apply_args o2 (p1 ** o1 ** END) in
		  if not (equivalence o2' o') then Lfcheck.mismatch_term env (get_pos o2') o2' (get_pos o') o';
	      | _ -> raise FalseWitness)
          | _ -> raise FalseWitness)
      | _ -> raise FalseWitness)
  | _ -> raise FalseWitness

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
