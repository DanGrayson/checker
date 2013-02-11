open Typesystem
open Lfcheck
open Printer
open Printf
open Errorcheck

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t args =
  if tactic_tracing then printf "assumption: t = %a\n%!" _t t;
  let rec repeat = function
    | (v,u) :: envp -> (
	try
	  Lfcheck.subtype env u t;
	  TacticSuccess(var_to_lf v)
	with SubtypeFailure -> 
	  repeat envp)
    | [] -> TacticFailure
  in repeat env.lf_context

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/assumption.cmo "
  End:
 *)
