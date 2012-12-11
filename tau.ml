open Error
open Variables
open Typesystem
open Names

let rec get_ts_type (v:var) (env:context) : atomic_expr = (
  match env with
  | (_, (pos, F_APPLY(F_hastype,[CAN(_,APPLY(V v',NIL)); CAN t]))) :: env 
    -> if v = v' then t else get_ts_type v env
  | _ :: env -> get_ts_type v env
  | [] -> raise Not_found
 )

let rec tau (pos:position) (env:context) (pos,e) : atomic_expr = 
  match e with
  | APPLY(V v,NIL) -> (
      try get_ts_type v env
      with Not_found -> raise (TypeCheckingFailure(env,pos, "unbound variable, not in TS context: " ^ vartostring v)))
  | APPLY(h,args) -> with_pos pos (
      match h with
      | TAC _ -> raise NotImplemented
      | V v -> 
	  let _ = get_ts_type v in
	  raise NotImplemented
      | U uh -> raise Internal		(* u-expression doesn't have a type *)
      | T th -> raise Internal		(* t-expression doesn't have a type *)
      | O oh -> (
	  match oh with
	  | O_u -> (
	      match args with 
	      | ARG(CAN u,NIL) -> Helpers.make_T_U (pos, (Helpers.make_U_next u))
	      | _ -> raise Internal)
	  | O_j -> (
	      match args with 
	      | ARG(CAN m1,ARG(CAN m2,NIL)) -> 
		  Helpers.make_T_Pi 
		    (with_pos_of m1 (Helpers.make_T_U m1))
		    (newunused(), (with_pos_of m2 (Helpers.make_T_U m2)))
	      | _ -> raise Internal)
	  | O_ev -> (
	      match args with 
	      | ARG(f,ARG(o,ARG(LAMBDA(x,t),NIL))) ->
		  (* ????  any use of "uncan" is suspect *)
		  unmark (Helpers.uncan (Substitute.subst (x,o) t))
	      | _ -> raise Internal)
	  | O_lambda -> (
	      match args with 
	      | ARG(CAN t,ARG(LAMBDA(x,CAN o),NIL)) ->
		  Helpers.make_T_Pi t (x, tau pos (ts_bind (x,t) env) o)
	      | _ -> raise Internal)
	  | O_forall -> (
	      match args with 
	      | ARG(CAN u,ARG(CAN u',_)) ->
		  Helpers.make_T_U (nowhere 6 (Helpers.make_U_max u u'))
	      | _ -> raise Internal)
	  | O_tt -> Helpers.make_T_Pt
	  | O_pair | O_pr1 | O_pr2 | O_total | O_pt | O_pt_r | O_coprod | O_ii1
	  | O_ii2 | O_sum | O_empty | O_empty_r | O_c | O_ip_r | O_ip
	  | O_paths | O_refl | O_J | O_rr0 | O_rr1
	    -> raise NotImplemented
	 )
     )

let tau env e = tau (no_pos 2) env e
