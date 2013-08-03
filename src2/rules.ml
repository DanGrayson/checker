(** Inference rules. *) (* -*- fill-column: 122 -*- *)

open Error
open Expressions

type rule_name =
    R_Empty | R_Abstr | R_TypeVar | R_Parm

module InferenceRules :
    sig
      type statement
      val rule : rule_name * statement list -> statement
    end =
  struct
    type statement = judgment list (* A list [h;i;j] represents the judgment j=>(i=>h).  In other words, it's a chain of
				      implications, stored in reverse order, with the final conclusion at the top of the
				      list.  If we were using contexts, we would write j,i |- h instead; we refrain from
				      separating the context from the final conclusion. *)
    let rule n = match n with
    | R_Empty, []			(* empty statement *)
      -> []
    | R_Abstr, [q :: p :: s]		(* abstraction *)
      -> J_Pi(p,q) :: s
    | R_TypeVar, [s]			(* new type variable or parameter *)
      -> J_istype(None) :: s
    | R_Parm, [J_istype(Some t) :: s]	(* new axiom or parameter *)
      -> J_hastype(t,None) :: s
    | _ -> raise InternalError
  end
