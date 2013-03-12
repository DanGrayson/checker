open Typesystem
open Lfcheck
open Names
open Error
open Printer
open Printf

(** fill in the third argument of @[ev][f,x,_] using tau *)
let ev3 (surr:surrounding) env pos t args =
  (* This code was formerly a part of the file fillin.ml, removed. *)
  match surr with
  | (env,_, Some (pos,APPLY( O O_ev, ARG(f,_))), _) :: _ -> (
      try
	let tf =
	  Tau.tau env f
	in (
	match Error.unmark tf with
	| APPLY(T T_Pi, ARG(_,ARG(t,END))) -> TacticSuccess t
	| _ -> raise (TypeCheckingFailure(
		      env, surr, [
		      get_pos f,
		      "expected a TS function:\n    " ^ ts_expr_to_string f ^
		      "\n  : " ^ ts_expr_to_string tf ])))

      with NotImplemented ->
	printf "warning: ev3: \"tau\" not implemented for %a\n%!" _e (env,f);
	TacticFailure)
  | _ ->
      printf "error: ev3 - unexpected surroundings:\n%!";
      print_surroundings surr;
      TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/ev3.cmo "
  End:
 *)
