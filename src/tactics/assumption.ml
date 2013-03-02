open Typesystem
open Printer
open Printf
open Errorcheck
open Variables

exception FoundOne of var

let type_equiv = Alpha.UEquivA.type_equiv empty_uContext

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t args =
  if Lfcheck.tactic_tracing then printf "assumption: t = %a\n%!" _t t;
  let rec repeat i = function
    | (v,u) :: envp -> (
	if type_equiv (i+1) u t
	then TacticSuccess(var_to_lf (VarRel i))
	else repeat (i+1) envp)
    | [] -> TacticFailure
  in repeat 0 env.lf_context

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/assumption.cmo "
  End:
 *)
