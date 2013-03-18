open Typesystem
open Printer
open Printf
open Errorcheck
open Variables
open Helpers

exception FoundOne of identifier

let type_equiv = Alpha.UEquivA.type_equiv empty_uContext

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t args =
  if Error.tactic_tracing then printf "tactic: assumption: t = %a\n%!" _t (env,t);
  let rec repeat i = function
    | (v,u) :: envp -> (
	if Lfcheck.is_subtype env (rel_shift_type (i+1) u) t
	then TacticSuccess(var_to_lf_bare (Rel i))
        else repeat (i+1) envp)
    | [] -> (
        try
          MapIdentifier.iter
            (fun v u -> if Lfcheck.is_subtype env u t then raise (FoundOne v)) (* this is probably too expensive to keep doing *)
            env.global_lf_context;
          TacticFailure
        with FoundOne v -> TacticSuccess(var_to_lf_bare (Var v))
	)
  in repeat 0 env.local_lf_context

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/assumption.cmo "
  End:
 *)
