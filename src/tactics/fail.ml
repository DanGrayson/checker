open Typesystem
open Lfcheck

(** a tactic that always fails *)
let fail surr env pos t args = TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/fail.cmo "
  End:
 *)
