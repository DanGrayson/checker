(** Filling in the unknown types in an expression, after parsing.

    For example, the third branch of [\[ev;x\](f,o,_)], written in short form
    [f o], needs to be filled in, based on the context, using [tau].

    This file is not completely implemented: some binders are ignored.
 *)

open Typesystem
open Tau
open Error
open Printer

let rec fillinlist pos env es = List.map (fillin' pos env) es
and fillin' pos env = function
  | LAMBDA(v,body) as l -> raise (Unimplemented_expr l)
  | ATOMIC e -> ATOMIC(fillin env e)
and fillin env (pos,e) = (pos, match e with
  | EmptyHole _ -> raise (TypingError(pos,"empty hole, no method for filling"))
  | Variable _ as v -> v
  | APPLY(label,branches) ->
      match label with
      | L _ -> e			(* bodies of definitions have been filled in previously *)
      | U _ -> e
      | O O_lambda -> (
	  match branches with 
	  | [ATOMIC t; LAMBDA( x, ATOMIC o)] -> 
	      Helpers.make_OO_lambda (fillin env t)  (x, fillin (ts_bind (x,t) env) o)
	  | _ -> raise Internal)
      | T ( T_Pi | T_Sigma ) -> (
	  match branches with 
	  | [ATOMIC t; LAMBDA( x,ATOMIC o)] -> 
	      Helpers.make_TT_Pi (fillin env t)  (x, fillin (ts_bind (x,t) env) o)
	  | _ -> raise (Internal_expr (ATOMIC (pos, e))))
      | O O_forall -> (
	  match branches with 
	  | [ATOMIC m; ATOMIC m'; ATOMIC n; LAMBDA( x,ATOMIC o)] -> 
	      Helpers.make_OO_forall m m' 
		(fillin env n)
		(x, fillin (ts_bind (x,(get_pos n, Helpers.make_TT_El n)) env) o)
	  | _ -> raise Internal)
      | O O_ev -> (
	  match branches with 
	    [ATOMIC f;ATOMIC p;LAMBDA(_,ATOMIC(_,EmptyHole _))] -> (
	      let tf = tau env f in
	      match unmark tf with
	      | APPLY(T T_Pi, [ATOMIC t1; LAMBDA( x, ATOMIC t2)])
		-> Helpers.make_OO_ev (fillin env f) (fillin env p) (x, (fillin (ts_bind (x,t1) env) t2))
	      | _ -> raise (TypeCheckingFailure(get_pos f,"expected a TS function:\n    " ^(ts_expr_to_string f) ^"\n  : "^(ts_expr_to_string tf))))
	  | [ATOMIC f; ATOMIC p; LAMBDA( x,ATOMIC t2)] ->
	      let p = fillin env p in
	      let t1 = tau env p in
	      Helpers.make_OO_ev (fillin env f) p (x, (fillin (ts_bind (x,t1) env) t2))
	  | _ -> APPLY (label, fillinlist pos env branches)
	 )
      | _ -> APPLY (label, fillinlist pos env branches))

