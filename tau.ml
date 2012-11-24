open Typesystem

let rec tau (pos:Error.position) env = function
    | LAMBDA _ -> raise Error.Internal
    | POS(pos,e) -> match e with 
      | EmptyHole _ -> raise (Error.TypingError(pos, "empty hole, type undetermined"))
      | Variable v -> (
	  try List.assoc v env.oc
	  with Not_found -> raise (Error.TypingError(pos, "unbound variable, not in context: " ^ (Printer.vartostring' v))))
      | APPLY(h,args) -> with_pos pos (
	  match h with
	  | Defapp _ -> raise Error.NotImplemented
	  | UU _ | TT _ -> raise Error.Internal
	  | OO oh -> match oh with
	    | OO_u -> (
		match args with 
		| [u] -> Helpers.make_TT_U (POS(pos, (Helpers.make_UU (UU_plus 1) [u])))
		| _ -> raise Error.Internal)
	    | OO_j -> (
		match args with 
		| [m1;m2] -> Helpers.make_TT_Pi (with_pos_of m1 (Helpers.make_TT_U m1)) ((Error.Nowhere,VarUnused), (with_pos_of m2 (Helpers.make_TT_U m2)))
		| _ -> raise Error.Internal)
	    | OO_ev -> (
		match args with 
		| [f;o;LAMBDA( x,t)] -> strip_pos (Substitute.subst [(strip_pos_var x,o)] t)
		| _ -> raise Error.Internal)
	    | OO_lambda -> (
		match args with 
		| [t;LAMBDA( x,o)] -> Helpers.make_TT_Pi t (x, tau pos (obind (x,t) env) o)
		| _ -> raise Error.Internal)
	    | OO_forall -> (
		match args with 
		| u :: u' :: _ -> Helpers.make_TT_U (nowhere (Helpers.make_UU UU_max [u; u']))
		| _ -> raise Error.Internal)
	    | OO_pair -> raise Error.NotImplemented
	    | OO_pr1 -> raise Error.NotImplemented
	    | OO_pr2 -> raise Error.NotImplemented
	    | OO_total -> raise Error.NotImplemented
	    | OO_pt -> raise Error.NotImplemented
	    | OO_pt_r -> raise Error.NotImplemented
	    | OO_tt -> Helpers.make_TT_Pt
	    | OO_coprod -> raise Error.NotImplemented
	    | OO_ii1 -> raise Error.NotImplemented
	    | OO_ii2 -> raise Error.NotImplemented
	    | OO_sum -> raise Error.NotImplemented
	    | OO_empty -> raise Error.NotImplemented
	    | OO_empty_r -> raise Error.NotImplemented
	    | OO_c -> raise Error.NotImplemented
	    | OO_ic_r -> raise Error.NotImplemented
	    | OO_ic -> raise Error.NotImplemented
	    | OO_paths -> raise Error.NotImplemented
	    | OO_refl -> raise Error.NotImplemented
	    | OO_J -> raise Error.NotImplemented
	    | OO_rr0 -> raise Error.NotImplemented
	    | OO_rr1 -> raise Error.NotImplemented
				 )
let tau = tau Error.Nowhere
