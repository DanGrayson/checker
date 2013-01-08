(** Tactics. *)

open Typesystem

let _ = add_tactic "ev3" Ev3.ev3
let _ = add_tactic "default" Default.default
let _ = add_tactic "a" Assumption.assumption
let _ = add_tactic "tn1" Tn.tn1

(* 
  Local Variables:
  compile-command: "make -C ../.. build "
  End:
 *)
