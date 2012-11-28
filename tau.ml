open Typesystem

let rec tau (pos:Error.position) env = function
    | LAMBDA _ -> raise Error.Internal
    | POS(pos,e) -> match e with 
      | EmptyHole _ -> raise (Error.TypingError(pos, "empty hole, type undetermined"))
      | Variable v -> (
	  try List.assoc v env.ts_context
	  with Not_found -> raise (Error.TypingError(pos, "unbound variable, not in context: " ^ (vartostring' v))))
      | APPLY(h,args) -> with_pos pos (
	  match h with
	  | VarDefined _ -> raise Error.Internal
	  | V _ -> raise Error.NotImplemented
	  | R _ | U _ | T _ -> raise Error.Internal
	  | O oh -> match oh with
	    | O_u -> (
		match args with 
		| [u] -> Helpers.make_TT_U (POS(pos, (Helpers.make_UU U_next [u])))
		| _ -> raise Error.Internal)
	    | O_j -> (
		match args with 
		| [m1;m2] -> Helpers.make_TT_Pi (with_pos_of m1 (Helpers.make_TT_U m1)) ((Error.Nowhere,VarUnused), (with_pos_of m2 (Helpers.make_TT_U m2)))
		| _ -> raise Error.Internal)
	    | O_ev -> (
		match args with 
		| [f;o;LAMBDA( x,t)] -> strip_pos (Substitute.subst [(strip_pos_var x,o)] t)
		| _ -> raise Error.Internal)
	    | O_lambda -> (
		match args with 
		| [t;LAMBDA( x,o)] -> Helpers.make_TT_Pi t (x, tau pos (obind (x,t) env) o)
		| _ -> raise Error.Internal)
	    | O_forall -> (
		match args with 
		| u :: u' :: _ -> Helpers.make_TT_U (nowhere (Helpers.make_UU U_max [u; u']))
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
