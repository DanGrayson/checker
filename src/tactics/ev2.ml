open Errorcheck open Tau open Substitute open Typesystem open Lfcheck 
open Names open Error open Printer open Printf open Variables open Helpers

(** fill in argument 2 of @[ev][f,x,_,U] using tau *)
let ev2 (surr:surrounding) env pos t args =
  match surr with 
  | (env,S_arg'(2,O(O_ev|O_ev'),ARG(x,ARG(f,_)),_), _, _) :: _ ->
	let tf = tau env f in (
	match unmark tf with
	| APPLY(T (T_Pi|T_Pi'), ARG(t,_)) -> TacticSuccess t
	| _ -> ts_function_expected env f tf)
  | _ -> TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/ev2.cmo "
  End:
 *)
