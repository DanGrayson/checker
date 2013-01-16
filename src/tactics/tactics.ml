(** Tactics. *)

open Typesystem

let _ = add_tactic "ev3" Ev3.ev3
let _ = add_tactic "default" Default.default
let _ = add_tactic "assumption" Assumption.assumption
let _ = add_tactic "fail" Fail.fail
let _ = add_tactic "admit" Admit.admit
let _ = add_tactic "apply" Apply.apply
let _ = add_tactic "tn1" Tn.tn1
let _ = add_tactic "tn12" Tn.tn12

(* 
  Local Variables:
  compile-command: "make -C ../.. build "
  End:
 *)
