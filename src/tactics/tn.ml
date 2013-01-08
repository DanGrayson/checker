(** tactics that insert the type of one of the following arguments*)

open Typesystem
open Error
open Names
open Helpers
open Printer

(** insert the type of the next argument *)
let tn1 surr env pos t =
  if not (Alpha.UEqual.type_equiv empty_uContext t texp)
  then raise (TypeCheckingFailure(env, surr, [ pos, "error: tactic tn1: expected a hole for a t-expression" ]));
  match surr with
  | (S_argument i, Some (pos, APPLY(head,args)), _) :: _ -> TacticSuccess (Tau.tau env (nth_arg (i+1) args))
  | _ -> TacticFailure

(** insert the type of either of the next two arguments *)
let tn12 surr env pos t =
  if not (Alpha.UEqual.type_equiv empty_uContext t texp)
  then raise (TypeCheckingFailure(
              env, surr, 
              [ pos, "error: tactic tn12: expected a hole of LF type texp" ;
                get_pos t, "but found a hole of type " ^ lf_type_to_string t
              ]));
  match surr with
  | (S_argument i, Some (pos, APPLY(head,args)), _) :: _ -> TacticSuccess (
      try
	Tau.tau env (nth_arg (i+1) args)
      with (NotImplemented | TypeCheckingFailure _) ->
	Tau.tau env (nth_arg (i+2) args)
     )
  | _ -> TacticFailure

let _ = add_tactic "tn1" tn1
let _ = add_tactic "tn12" tn12

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/tn.cmo "
  End:
 *)

