(** This tactic attempts to fill an empty hole of type [wexp] with an appropriate witness to the proof. *)

open Names
open Variables
open Printer
open Printf
open Typesystem
open Lfcheck
open Error

let witness (surr:surrounding) (env:context) (pos:position) (t:lf_type) (args:spine) : tactic_return = 
  match surr with 
  | (S_argument 1, None, Some j) :: _ -> (
      match unmark j with
      | F_Apply(F_witnessed_hastype,[_;o;t]) -> (
	  (* printf " ? : %a : %a\n%!" _e o _e t; *)
	  match unmark o with
	  | APPLY(V v, END) -> (
	      let p = witness_var v in
	      TacticSuccess (var_to_lf_pos (get_pos o) p)
	     )
	  | _ -> TacticFailure
	 )
      | _ -> raise NotImplemented)
  | _ -> raise NotImplemented

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/witness.cmo "
  End:
 *)
