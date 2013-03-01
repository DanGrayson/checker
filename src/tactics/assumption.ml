open Typesystem
open Lfcheck
open Printer
open Printf
open Errorcheck
open Variables

exception FoundOne of var

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t args =
  if tactic_tracing then printf "assumption: t = %a\n%!" _t t;
  let rec repeat = function
    | (v,u) :: envp -> (
	if is_subtype env u t
	then TacticSuccess(var_to_lf v)
	else repeat envp)
    | [] -> (
	try
	  VarMap.iter
	    (fun v u -> if is_subtype env u t then raise (FoundOne v))
	    env.global_lf_context;
	  TacticFailure
	with FoundOne v -> TacticSuccess(var_to_lf v)
	)
  in repeat env.lf_context

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/assumption.cmo "
  End:
 *)
