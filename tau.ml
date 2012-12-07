open Error
open Typesystem
open Names

let rec get_ts_type (v:var) (env:context) : ts_expr = (
  match env with
  | (_, (pos, F_APPLY(F_hastype,[Phi(_,APPLY(V v',[])); Phi t]))) :: env 
    -> if v = v' then t else get_ts_type v env
  | _ :: env -> get_ts_type v env
  | [] -> raise Not_found
 )

let rec tau (pos:position) (env:context) (pos,e) : ts_expr = 
  match e with
  | TacticHole n -> raise NotImplemented
  | EmptyHole _ -> raise (TypeCheckingFailure(env, pos, "empty hole, type undetermined"))
  | APPLY(V v,[]) -> (
      try get_ts_type v env
      with Not_found -> raise (TypeCheckingFailure(env,pos, "unbound variable, not in TS context: " ^ (vartostring v))))
  | APPLY(h,args) -> with_pos pos (
      match h with
      | V v -> 
	  let _ = get_ts_type v in
	  raise NotImplemented
      | U uh -> raise Internal		(* u-expression doesn't have a type *)
      | T th -> raise Internal		(* t-expression doesn't have a type *)
      | O oh -> (
	      match oh with
	    | O_u -> (
		match args with 
		| [Phi u] -> Helpers.make_TT_U (pos, (Helpers.make_UU U_next [Phi u]))
		| _ -> raise Internal)
	    | O_j -> (
		match args with 
		| [Phi m1;Phi m2] -> Helpers.make_TT_Pi (with_pos_of m1 (Helpers.make_TT_U m1)) (VarUnused, (with_pos_of m2 (Helpers.make_TT_U m2)))
		| _ -> raise Internal)
	    | O_ev -> (
		match args with 
		| [f; o; LAMBDA(x,t)] -> unmark (Substitute.atomic (Substitute.subst (x,o) t)) (* ????  any use of "atomic" is suspect *)
		| _ -> raise Internal)
	    | O_lambda -> (
		match args with 
		| [Phi t;LAMBDA(x,Phi o)] -> Helpers.make_TT_Pi t (x, tau pos (ts_bind (x,t) env) o)
		| _ -> raise Internal)
	    | O_forall -> (
		match args with 
		| Phi u :: Phi u' :: _ -> Helpers.make_TT_U (nowhere 6 (Helpers.make_UU U_max [Phi u; Phi u']))
		| _ -> raise Internal)
	    | O_pair -> raise NotImplemented
	    | O_pr1 -> raise NotImplemented
	    | O_pr2 -> raise NotImplemented
	    | O_total -> raise NotImplemented
	    | O_pt -> raise NotImplemented
	    | O_pt_r -> raise NotImplemented
	    | O_tt -> Helpers.make_TT_Pt
	    | O_coprod -> raise NotImplemented
	    | O_ii1 -> raise NotImplemented
	    | O_ii2 -> raise NotImplemented
	    | O_sum -> raise NotImplemented
	    | O_empty -> raise NotImplemented
	    | O_empty_r -> raise NotImplemented
	    | O_c -> raise NotImplemented
	    | O_ip_r -> raise NotImplemented
	    | O_ip -> raise NotImplemented
	    | O_paths -> raise NotImplemented
	    | O_refl -> raise NotImplemented
	    | O_J -> raise NotImplemented
	    | O_rr0 -> raise NotImplemented
	    | O_rr1 -> raise NotImplemented
	 )
     )

let tau env e = tau (no_pos 2) env e
