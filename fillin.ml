(** Filling in the unknown types in an expression, after parsing.

    For example, the third branch of [\[ev;x\](f,o,_)], written in short form
    [f o], needs to be filled in, based on the context, using [tau].

    This file is not completely implemented: some binders are ignored.
 *)

open Typesystem

let rec fillinlist pos env es = List.map (fillin pos env) es
and fillin pos env = function
    | POS(pos,e) -> POS(pos, fillin pos env e)
    | TT_variable _ as t -> t
    | OO_variable _ as o -> o
    | UU _ as u -> u
    | Expr(label,branches) -> (
	match label with
(*
	| BB _ -> raise InternalError (* what type do we bind the variable to? *)
*)
	| OO OO_emptyHole | OO OO_numberedEmptyHole _ -> raise (TypingError(pos,"empty o-expression hole, no method for filling"))
	| TT TT_EmptyHole | TT TT_NumberedEmptyHole _ -> raise (TypingError(pos,"empty t-expression hole, no method for filling"))
	| OO OO_ev -> (
	    match branches with 
	      [f;p] -> (
		match strip_pos(Tau.tau env f) with
		| Expr(TT TT_Pi, [t1; Expr(BB ((pos,v) as x),[t2])])
		  -> Expr(OO OO_ev, [fillin pos env f; 
				  fillin pos env p; 
				  fillin pos (obind (v,t1) env) (make_BB1 x t2)])
		| _ -> raise (TypingError(get_pos f,"expected a product type")))
	    | _ -> Expr (label, fillinlist pos env branches)
	   )
	| _ -> Expr (label, fillinlist pos env branches)
       )

let fillin = fillin Nowhere
