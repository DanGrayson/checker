(** Filling in the unknown types in an expression, after parsing.

    For example, the third branch of [\[ev;x\](f,o,_)], written in short form
    [f o], needs to be filled in, based on the context, using [tau].

    This file is not completely implemented: some binders are ignored.
 *)

open Error
open Typesystem
open Names
open Tau
open Printer

let rec fillinlist pos env es = List.map (fillin' pos env) es
and fillin' pos env = function
  | LAMBDA(v,body) as l -> raise (Unimplemented_expr l)
  | Phi e -> Phi(fillin env e)
and fillin env (pos,e) = (pos, match e with
  | TacticHole n -> raise NotImplemented
  | EmptyHole _ -> raise (TypeCheckingFailure(env,pos,"empty hole, no method for filling"))
  | APPLY(V _,[]) as v -> v
  | APPLY(label,branches) ->
      match label with
      | V _ -> e			(* bodies of definitions have been filled in previously *)
      | U _ -> e
      | O O_lambda -> (
	  match branches with 
	  | [Phi t; LAMBDA( x, Phi o)] -> 
	      Helpers.make_OO_lambda (fillin env t)  (x, fillin (ts_bind (x,t) env) o)
	  | _ -> raise Internal)
      | T ( T_Pi | T_Sigma ) -> (
	  match branches with 
	  | [Phi t; LAMBDA( x,Phi o)] -> 
	      Helpers.make_TT_Pi (fillin env t)  (x, fillin (ts_bind (x,t) env) o)
	  | _ -> raise (Internal_expr (Phi (pos, e))))
      | O O_forall -> (
	  match branches with 
	  | [Phi m; Phi m'; Phi n; LAMBDA( x,Phi o)] -> 
	      Helpers.make_OO_forall m m' 
		(fillin env n)
		(x, fillin (ts_bind (x,(get_pos n, Helpers.make_TT_El n)) env) o)
	  | _ -> raise Internal)
      | O O_ev -> (
	  match branches with 
	    [Phi f;Phi p;LAMBDA(_,Phi(_,EmptyHole _))] -> (
	      let tf = tau env f in
	      match unmark tf with
	      | APPLY(T T_Pi, [Phi t1; LAMBDA( x, Phi t2)])
		-> Helpers.make_OO_ev (fillin env f) (fillin env p) (x, (fillin (ts_bind (x,t1) env) t2))
	      | _ -> raise (TypeCheckingFailure(env,get_pos f,"expected a TS function:\n    " ^(ts_expr_to_string f) ^"\n  : "^(ts_expr_to_string tf))))
	  | [Phi f; Phi p; LAMBDA( x,Phi t2)] ->
	      let p = fillin env p in
	      let t1 = tau env p in
	      Helpers.make_OO_ev (fillin env f) p (x, (fillin (ts_bind (x,t1) env) t2))
	  | _ -> APPLY (label, fillinlist pos env branches)
	 )
      | _ -> APPLY (label, fillinlist pos env branches))

