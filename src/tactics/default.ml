open Helpers
open Error
open Typesystem
open Lfcheck
open Printer
open Printf

let other_tactics : (string * tactic_function) list = [
  "ev2", Ev2.ev2;
  "ev3", Ev3.ev3;
]

let try_other_tactics surr env pos t args =
  if tactic_tracing then printf "tactic: try_other_tactics: t = %a\n%!" _t (env,t);
  let rec repeat tactics =
    match tactics with 
    | (name,tactic) :: tactics -> (
	if tactic_tracing then printf "tactic: %s: t = %a\n%!" name _t (env,t);
	match tactic surr env pos t args 
	with 
	| TacticFailure -> repeat tactics
	| success -> success)
    | [] -> TacticFailure
  in repeat other_tactics

let rec default surr env pos t args =
  if tactic_tracing then printf "tactic: default: t = %a\n%!" _t (env,t);
  match unmark t with
  | J_Singleton(e,_) -> TacticSuccess e
  | J_Pi(v,a,b) -> (
      let e0 = pos, TEMPLATE(v,(pos,default_tactic)) in
      let surr = (env,S_body,Some e0,Some t) :: surr in
      match default surr (local_lf_bind env v a) (get_pos t) b args with
      | TacticSuccess e -> TacticSuccess (with_pos pos (TEMPLATE(v,e)))
      | TacticFailure as r -> r)
  | J_Basic((J_hastype|J_istype),_) -> Assumption.assumption surr env pos t args
  | J_Basic(J_wexp,[]) -> 
      if tactic_tracing then printf "tactic: witness: t = %a\n%!" _t (env,t);
      Witness.witness surr env pos t args
  | _ -> try_other_tactics surr env pos t args

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/default.cmo "
  End:
 *)
