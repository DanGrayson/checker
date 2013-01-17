open Typesystem
open Lfcheck

(** admit the current tactic term, unchanged, as satisfactory for type checking

    Not completely implemented, in that the routine path_equivalence may raise
    an exception. *)
let admit surr env pos t args = TacticSuccess (pos, APPLY(ADMISSION t, END))

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/admit.cmo "
  End:
 *)
