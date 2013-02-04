open Error
open Typesystem
open Lfcheck
open Printer
open Printf

let rec default surr env pos t args = 
  if tactic_tracing then printf "default: t = %a\n%!" _t t;
  match unmark t with
  | F_Singleton(e,_) -> TacticSuccess e
  | F_Pi(v,a,b) -> (
      match default surr (lf_bind env v a) (get_pos t) b args with 
      | TacticSuccess e -> TacticSuccess (with_pos pos (LAMBDA(v,e)))
      | TacticFailure as r -> r)
  | F_Apply((F_hastype|F_istype),_) -> Assumption.assumption surr env pos t args
  | F_Apply(F_wexp,[]) -> Witness.witness surr env pos t args
  | _ -> TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/default.cmo "
  End:
 *)
