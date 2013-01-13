(** Tactics. *)

open Typesystem

let _ = add_tactic "ev3" Ev3.ev3
let _ = add_tactic "default" Default.default
let _ = add_tactic "assumption" Assumption.assumption
let _ = add_tactic "fail" Fail.fail
let _ = add_tactic "admit" Admit.admit

open Tn

(* 
  Local Variables:
  compile-command: "make -C ../.. build "
  End:
 *)
