open Typesystem

let rec get_ts_type (v:var') (env:context) : ts_expr = (
  match env with
  | (_, (pos, F_APPLY(F_hastype,[ATOMIC(_,Variable v'); ATOMIC t]))) :: env -> if v = v' then t else get_ts_type v env
  | _ :: env -> get_ts_type v env
  | [] -> raise Not_found
 )

let rec tau (pos:Error.position) (env:context) (pos,e) : atomic_term = match e with
  | EmptyHole _ -> raise (Error.TypingError(pos, "empty hole, type undetermined"))
  | Variable v -> (
      try get_ts_type v env
      with Not_found -> raise (Error.TypingError(pos, "unbound variable, not in context: " ^ (vartostring' v))))
  | APPLY(h,args) -> with_pos pos (
      match h with
      | L _ -> raise Error.NotImplemented
      | R _ | U _ | T _ -> raise Error.Internal
      | O oh -> match oh with
	| O_u -> (
	    match args with 
	    | [ATOMIC u] -> Helpers.make_TT_U (pos, (Helpers.make_UU U_next [ATOMIC u]))
	    | _ -> raise Error.Internal)
	| O_j -> (
	    match args with 
	    | [ATOMIC m1;ATOMIC m2] -> Helpers.make_TT_Pi (with_pos_of m1 (Helpers.make_TT_U m1)) ((Error.Nowhere,VarUnused), (with_pos_of m2 (Helpers.make_TT_U m2)))
	    | _ -> raise Error.Internal)
	| O_ev -> (
	    match args with 
	    | [ATOMIC f;ATOMIC o;LAMBDA(x,ATOMIC t)] -> strip_pos (Substitute.subst [(strip_pos x,o)] t)
	    | _ -> raise Error.Internal)
	| O_lambda -> (
	    match args with 
	    | [ATOMIC t;LAMBDA(x,ATOMIC o)] -> Helpers.make_TT_Pi t (x, tau pos (ts_bind (x,t) env) o)
	    | _ -> raise Error.Internal)
	| O_forall -> (
	    match args with 
	    | ATOMIC u :: ATOMIC u' :: _ -> Helpers.make_TT_U (nowhere (Helpers.make_UU U_max [ATOMIC u; ATOMIC u']))
	    | _ -> raise Error.Internal)
	| O_pair -> raise Error.NotImplemented
	| O_pr1 -> raise Error.NotImplemented
	| O_pr2 -> raise Error.NotImplemented
	| O_total -> raise Error.NotImplemented
	| O_pt -> raise Error.NotImplemented
	| O_pt_r -> raise Error.NotImplemented
	| O_tt -> Helpers.make_TT_Pt
	| O_coprod -> raise Error.NotImplemented
	| O_ii1 -> raise Error.NotImplemented
	| O_ii2 -> raise Error.NotImplemented
	| O_sum -> raise Error.NotImplemented
	| O_empty -> raise Error.NotImplemented
	| O_empty_r -> raise Error.NotImplemented
	| O_c -> raise Error.NotImplemented
	| O_ic_r -> raise Error.NotImplemented
	| O_ic -> raise Error.NotImplemented
	| O_paths -> raise Error.NotImplemented
	| O_refl -> raise Error.NotImplemented
	| O_J -> raise Error.NotImplemented
	| O_rr0 -> raise Error.NotImplemented
	| O_rr1 -> raise Error.NotImplemented
     )

let tau = tau Error.Nowhere
