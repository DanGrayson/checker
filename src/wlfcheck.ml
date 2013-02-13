(** Check witnessed judgments for correctness. *)

open Variables
open Typesystem
open Printer
open Printf
open Error
open Helpers
open Names
open Errorcheck

let mismatch_term_tstype_tstype env e s t =
  raise (TypeCheckingFailure (env, [], [
               get_pos e, "error: expected term\n\t" ^ ts_expr_to_string e;
               get_pos s, "of type\n\t" ^ ts_expr_to_string s;
               get_pos t, "to be compatible with type\n\t" ^ ts_expr_to_string t]))

let equality = Alpha.UEqual.term_equiv empty_uContext
    (* Here equality is alpha-equivalence *)

let equivalence = equality
    (* We still have to implement the relation called ~ in the paper, which ignores inessential subterms. *)
    (* For now we use equality. *)

let compare_var_to_expr v e =
  match unmark e with
  | APPLY(V w, END) -> v = w
  | _ -> false

let open_context t1 (env,p,o,t2) =
  let v = newfresh (Var "x") in
  let v' = newfresh (Var_wd "x") in
  let env = tts_bind env v' v t1 in
  let e = var_to_lf v' ** var_to_lf v ** END in 
  let p = Substitute.apply_args p e in
  let o = Substitute.apply_args o e in
  let t2 = Substitute.apply_args t2 e in
  (env,p,o,t2)

let unpack_El' t =
  match unmark t with
  | APPLY(T T_El',args) -> args2 args
  | _ -> raise FalseWitness

let unpack_Pi' t =
  match unmark t with
  | APPLY(T T_Pi',args) -> args2 args
  | _ -> raise FalseWitness

let unpack_ev' o =
  match unmark o with
  | APPLY(O O_ev',args) -> args4 args
  | _ -> raise FalseWitness

let unpack_lambda' o =
  match unmark o with
  | APPLY(O O_lambda',args) -> args2 args
  | _ -> raise FalseWitness

let apply_2 f x y = Substitute.apply_args f (x ** y ** END)

let rec check_istype env t =
  if not (List.exists (fun (v,u) -> equivalence t u) env.ts_context)
  then 
    match unmark t with
    | APPLY(T th, args) -> (
	match th with
	| T_Pi' -> 
	    let t1,t2 = args2 args in
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
	    let o,p = args2 args in
	    check_hastype env p o uuu
	| T_Proof ->
	    let p,o,t = args3 args in
	    check_hastype env p o t
	| _ -> err env (get_pos t) "invalid type, or not implemented yet.")
    | _ -> err env (get_pos t) ("invalid type, or not implemented yet: " ^ ts_expr_to_string t)

and check_hastype env p o t =
  if false then printf "check_hastype\n p = %a\n o = %a\n t = %a\n%!" _e p _e o _e t;
  match unmark p with
  | APPLY(V (Var_wd _ | VarGen_wd _ as w), END) -> (
      let o',t' = 
	try tts_fetch_w w env
	with Not_found -> err env (get_pos p) "variable not in context" in
      if not (compare_var_to_expr o' o) then err env (get_pos o) ("expected variable " ^ vartostring o');
      if not (equivalence t t') then mismatch_term_tstype_tstype env o t' t)
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_wev ->
	  let pf,po = args2 pargs in
          let f,o,t1,t2 = unpack_ev' o in
          check_hastype env po o t1;
          let u = nowhere 123 (APPLY(T T_Pi', t1 ** t2 ** END)) in
          check_hastype env pf f u;
          let t2' = Substitute.apply_args t2 (po ** o ** END) in
          if not (equivalence t2' t) then mismatch_term_tstype_tstype env o t t2'
      | W_wlam -> 
	  let p = args1 pargs in
	  let t1',o = unpack_lambda' o in
	  let t1,t2 = unpack_Pi' t in
	  if not (equivalence t1' t1) then mismatch_term env (get_pos t) t (get_pos t1) t1;
	  let env,p,o,t2 = open_context t1 (env,p,o,t2) in
	  check_hastype env p o t2
      | W_wconv | W_wconveq | W_weleq | W_wpi1 | W_wpi2 | W_wl1 | W_wl2 | W_wevt1 | W_wevt2
      | W_wevf | W_wevo | W_wbeta | W_weta | W_Wsymm | W_Wtrans | W_wrefl | W_wsymm | W_wtrans
      | W_Wrefl
	-> raise FalseWitness
     )
  | _ -> err env (get_pos p) ("expected a witness expression: " ^ lf_expr_to_string p)

and check_type_equality env p t t' =
  match unmark p with
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_weleq ->
	  let peq = args1 pargs in
	  let o,p = unpack_El' t in
	  let o',p' = unpack_El' t' in
	  check_object_equality env peq o o' uuu;
	  check_hastype env p o uuu;
	  check_hastype env p' o' uuu
      | W_wrefl | W_Wrefl | W_Wsymm | W_Wtrans | W_wsymm | W_wtrans | W_wconv
      | W_wconveq | W_wpi1 | W_wpi2 | W_wlam | W_wl1 | W_wl2 | W_wev
      | W_wevt1 | W_wevt2 | W_wevf | W_wevo | W_wbeta | W_weta
	-> raise FalseWitness
     )
  | _ -> err env (get_pos p) ("expected a witness expression: " ^ lf_expr_to_string p)


and check_object_equality env p o o' t =
  match unmark p with
  | APPLY(W wh, pargs) -> (
      match wh with 
      | W_wbeta ->
	  let p1,p2 = args2 pargs in
	  let f,o1,t1',t2 = unpack_ev' o in
	  let t1,o2 = unpack_lambda' f in
	  if not (equivalence t1 t1') then mismatch_term env (get_pos t1) t1 (get_pos t1') t1';
	  check_hastype env p1 o1 t1;
	  let env,p2',o2',t2' = open_context t1 (env,p2,o2,t2) in
	  check_hastype env p2' o2' t2';
	  let t2'' = apply_2 t2 p1 o1 in
	  if not (equivalence t2'' t) then mismatch_term env (get_pos t2'') t2'' (get_pos t) t;
	  let o2' = apply_2 o2 p1 o1 in
	  if not (equivalence o2' o') then mismatch_term env (get_pos o2') o2' (get_pos o') o'
      | W_wrefl -> (
	  let p,p' = args2 pargs in
	  check_hastype env p o t;
	  check_hastype env p' o' t;
	  if not (equivalence o o') then mismatch_term env (get_pos o) o (get_pos o') o';
	 )
      | _ -> raise FalseWitness)
  | _ -> raise FalseWitness

let check (env:environment) (t:lf_type) =
  try
    match unmark t with 
    | F_Apply(F_istype,[t]) -> check_istype env t
    | F_Apply(F_witnessed_istype,[w;t]) -> raise NotImplemented
    | F_Apply(F_witnessed_hastype,[w;o;t]) -> check_hastype env w o t
    | F_Apply(F_witnessed_type_equality,[w;t;t']) -> check_type_equality env w t t'
    | F_Apply(F_witnessed_object_equality,[w;o;o';t]) -> check_object_equality env w o o' t
    | _ -> err env (get_pos t) "expected a witnessed judgment"
  with
    FalseWitness -> err env (get_pos t) "incorrect witness"

(* 
  Local Variables:
  compile-command: "make -C .. src/wlfcheck.cmo "
  End:
 *)
