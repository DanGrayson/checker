open Typesystem
open Lfcheck
open Printer
open Printf

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t args =
  if tactic_tracing then printf "assumption: t = %a\n%!" _t t;
  let rec repeat = function
    | (v,u) :: envp -> (
	try
	  Lfcheck.type_equivalence env t u;
	  TacticSuccess(var_to_lf v)
	with TypeEquivalenceFailure -> 
	  repeat envp)
    | [] -> TacticFailure
  in repeat env.lf_context

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/assumption.cmo "
  End:
 *)
