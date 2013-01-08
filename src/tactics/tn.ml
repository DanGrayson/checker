(** tactics that insert the type of one of the following arguments*)

open Typesystem
open Error
open Names
open Helpers
open Printer

let tn1 surr env pos t =
  if not (Alpha.UEqual.type_equiv empty_uContext t texp)
  then raise (TypeCheckingFailure(env, surr, [ pos, "error: tactic tn1: expected a hole for a t-expression" ]));
  match surr with
  | (S_argument i, Some (pos, APPLY(head,args)), _) :: _ -> TacticSuccess (Tau.tau env (nth_arg (i+1) args))
  | _ -> TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/tn.cmo "
  End:
 *)

