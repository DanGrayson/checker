open Typesystem
open Lfcheck
open Names
open Error
open Printer
open Printf
open Variables
open Helpers

(** fill in argument 3 of @[ev][f,x,T,_] using tau *)
let ev3 (surr:surrounding) env pos t args =
  match surr with
  | (env,S_argument 3, Some (pos,APPLY( O ( O_ev | O_ev' ), ARG(f,_))), _) :: _ -> (
      try
	let tf =
	  Tau.tau env f
	in (
	match Error.unmark tf with
	| APPLY(T ( T_Pi | T_Pi' ), ARG(_,ARG(t,END))) -> TacticSuccess t
	| _ -> raise (TypeCheckingFailure(
		      env, surr, [
		      get_pos f,
		      "ev3: expected a TS function:\n    " ^ ts_expr_to_string env f ^
		      "\n  : " ^ ts_expr_to_string env tf ])))

      with NotImplemented -> TacticFailure)
  | _ :: _ :: (env,S_argument 3, Some (pos,APPLY( O ( O_ev | O_ev' ), ARG(f,_))), _) :: _ -> (
      try
	let tf =
	  Tau.tau env f
	in (
	match Error.unmark tf with
	| APPLY(T ( T_Pi | T_Pi' ), ARG(_,ARG(t,END))) -> 
	    let t = Substitute.apply_args t (var_to_lf (VarRel 1) ** var_to_lf (VarRel 0) ** END) in
	    TacticSuccess t
	| _ -> raise (TypeCheckingFailure(
		      env, surr, [
		      get_pos f,
		      "ev3: expected a TS function:\n    " ^ ts_expr_to_string env f ^
		      "\n  : " ^ ts_expr_to_string env tf ])))

      with NotImplemented -> TacticFailure)
  | _ -> TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/ev3.cmo "
  End:
 *)
