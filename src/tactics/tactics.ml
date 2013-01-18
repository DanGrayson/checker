(** Tactics. *)

open Typesystem

let _ = List.iter add_tactic [
  "ev3", Ev3.ev3;
  "default", Default.default;
  "assumption", Assumption.assumption;
  "fail", Fail.fail;
  (* "admit", Admit.admit; *)
  "apply", Apply.apply;
  "tn1", Tn.tn1;
  "tn12", Tn.tn12;
  "check", Check.check
] 

(* 
  Local Variables:
  compile-command: "make -C ../.. build "
  End:
 *)
