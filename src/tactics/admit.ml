open Typesystem
open Lfcheck

(** find the first variable in the context of the right type and return it *)
let admit surr env pos t args = TacticSuccess (pos, APPLY(ADMISSION t, END))

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/admit.cmo "
  End:
 *)
