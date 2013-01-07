open Error
open Typesystem
open Lfcheck

let rec default surr env pos t = 
  match unmark t with
  | F_Singleton(e,_) -> TacticSuccess e
  | F_Pi(v,a,b) -> (
      match default surr ((v,a) :: env) (get_pos t) b with 
      | TacticSuccess e -> TacticSuccess (with_pos pos (LAMBDA(v,e)))
      | TacticFailure -> TacticFailure)
  | F_Apply((F_hastype|F_istype),_) -> Assumption.assumption surr env pos t
  | _ -> TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/default.cmo "
  End:
 *)
