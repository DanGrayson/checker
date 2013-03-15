open Helpers
open Error
open Typesystem
open Lfcheck
open Printer
open Printf

let other_tactics : tactic_function list = [Ev3.ev3]

let try_other_tactics surr env pos t args =
  let rec repeat tactics =
    match tactics with 
    | tactic :: tactics -> (
	match tactic surr env pos t args 
	with 
	| TacticFailure -> repeat tactics
	| success -> success)
    | [] -> TacticFailure
  in repeat other_tactics

let rec default surr env pos t args =
  if tactic_tracing then printf "default: t = %a\n%!" _t (env,t);

  match unmark t with
  | F_Singleton(e,_) -> TacticSuccess e
  | F_Pi(v,a,b) -> (
      let e0 = pos, LAMBDA(v,(pos,default_tactic)) in
      let surr = (env,S_body,Some e0,Some t) :: surr in
      match default surr (local_lf_bind env v a) (get_pos t) b args with
      | TacticSuccess e -> TacticSuccess (with_pos pos (LAMBDA(v,e)))
      | TacticFailure as r -> r)
  | F_Apply((F_hastype|F_istype),_) -> Assumption.assumption surr env pos t args
  | F_Apply(F_hastype_witness,[o;t]) -> (
      try TacticSuccess (Witness.find_w_hastype env o t)
      with Witness.WitnessNotFound -> TacticFailure)
  | F_Apply(F_object_equality_witness,[o;o';t]) -> (
      try TacticSuccess (Witness.find_w_object_equality env o o' t)
      with Witness.WitnessNotFound -> TacticFailure)
  | F_Apply(F_type_equality_witness,[t;t']) -> (
      try TacticSuccess (Witness.find_w_type_equality env t t')
      with Witness.WitnessNotFound -> TacticFailure)
  | F_Apply(F_wexp,[]) -> Witness.witness surr env pos t args
  | _ -> 

  match try_other_tactics surr env pos t args with
  | TacticSuccess _ as r -> r
  | TacticFailure ->

      TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/default.cmo "
  End:
 *)
