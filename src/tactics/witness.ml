(** This tactic attempts to fill an empty hole of type [wexp] with an appropriate witness to the proof. *)

open Helpers
open Names
open Variables
open Printer
open Printf
open Typesystem
open Lfcheck
open Error

let rec find_w_hastype env o t : tactic_return = (
  match unmark o with
  | APPLY(V v, END) -> (
      let p = witness_var v in
      TacticSuccess (var_to_lf_pos (get_pos o) p)
     )
  | APPLY(O O_ev',args) -> (
      let (f,o,t1,t2) = args4 args in
      let tf = nowhere 1232 (APPLY(T T_Pi', t1 ** t2 ** END)) in
      match find_w_hastype env f tf with
      | TacticSuccess pf -> (
	  match find_w_hastype env o t1 with
	  | TacticSuccess po ->
	      let w = make_W_wev pf po in
	      TacticSuccess (nowhere 201 w)
	  | f -> f)
      | f -> f)
  | _ -> TacticFailure
 )

let witness (surr:surrounding) (env:context) (pos:position) (t:lf_type) (args:spine) : tactic_return = 
  match surr with 
  | (S_argument 1, None, Some j) :: _ -> (
      match unmark j with
      | F_Apply(F_witnessed_hastype,[_;o;t]) -> find_w_hastype env o t
      | _ -> TacticFailure)
  | (S_argument 1, Some t, None) :: (S_argument 1, None, Some j) :: _ -> (
      match unmark j with
      | F_Apply(F_istype,[_]) -> (
	  match unmark t with 
	  | APPLY(T T_El', ARG(o, _)) -> find_w_hastype env o uuu
	  | _ -> TacticFailure)
      | _ -> TacticFailure)
  | _ -> TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/witness.cmo "
  End:
 *)
