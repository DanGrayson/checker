(** Exceptions, experiments, error message handling, and source code positions. *)

include Positions

let show_rules = false

let show_definitions = true

let try_normalization = true

let env_limit = Some 20

let tactic_tracing = false

let lesser_debug_mode = true

let debug_mode = ref false

let debug_subst = false

let new_counter () = let n = ref 0 in fun () -> incr n; !n

let proof_general_mode = ref false

let notail x = x			(* insert into code to termporarily prevent tail recursion *)

let error_count = ref 0

exception DebugMe
exception GeneralError of string
exception NotImplemented
exception Unimplemented of string
exception VariableNotInContext
exception NoMatchingRule
exception Eof
exception FalseWitness
exception GoBack of int
exception GoBackTo of int
exception NonSynthesizing

let bump_error_count pos =
  incr error_count;
  if not !proof_general_mode && !error_count >= 5 then (
    Printf.fprintf stderr "%s: too many errors, exiting.\n%!" (errfmt pos);
    raise (Failure "exiting"));
  flush stderr; flush stdout		(*just in case*)

(*
  Local Variables:
  compile-command: "make -C .. src/error.cmo "
  End:
 *)
