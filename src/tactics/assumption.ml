open Typesystem
open Lfcheck

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t =
  let rec repeat = function
    | (v,u) :: envp -> (
	try
	  Lfcheck.type_equivalence env t u;
	  TacticSuccess(var_to_lf v)
	with TypeEquivalenceFailure -> 
	  repeat envp)
    | [] -> TacticFailure
  in repeat env

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/assumption.cmo "
  End:
 *)
