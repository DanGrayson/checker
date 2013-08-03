(** Inference rules. *) (* -*- fill-column: 122 -*- *)

open Error
open Expressions

type rule_name =

  | R_Empty | R_Abstr | R_TypeVar | R_Parm | R_TypeEquality | R_ObjectEquality | R_TypeRefl | R_ObjectRefl | R_Wrefl
  | R_Wsymm | R_Wtrans

module InferenceRules :
    sig
      type statement
      val expose : statement -> judgment list
      val rule : rule_name * statement list -> statement
    end =
  struct
    type statement = judgment list (* A list [h;i;j] represents the judgment j=>(i=>h).  In other words, it's a chain of
				      implications, stored in reverse order, with the final conclusion at the top of the
				      list.  If we were using contexts, we would write j,i |- h instead; we refrain from
				      separating the context from the final conclusion. *)
    let expose s = s
    let rule n = match n with
    | R_Empty, [] ->			(* empty statement *)
	[]
    | R_Abstr, [q :: p :: s] ->		(* abstraction *)
	J_Pi(p,q) :: s
    | R_TypeVar, [s] ->			(* assume we are given a type *)
	J_istype(None) :: s
    | R_Parm, [J_istype(Some t) :: s] -> (* assume a type has an element *)
	J_hastype(t,None) :: s
    | R_TypeEquality, [J_istype(Some t) :: s; J_istype(Some t') :: s'] -> (* assume two types are equal *)
	if s == s' 
	then J_type_equality(t,t',None) :: s
	else raise InternalError
    | R_ObjectEquality, [J_hastype(t,Some o) :: s; J_hastype(t',Some o') :: s'] -> (* assume two objects are equal *)
	if s == s' && t == t'
	then J_object_equality(t,o,o',None) :: s
	else raise InternalError
    | R_Wrefl, [J_istype(Some t) :: s; J_istype(Some t') :: s'] -> (* record that two types are equal *)
	if s == s' && t = t'
	then J_type_equality(t,t',Some(BASIC(W_Wrefl,END))) :: s
	else raise InternalError
    | R_Wsymm, [J_type_equality(t,t',Some p) :: s]
      -> (* symmetry of type equality *)
	J_type_equality(t',t,Some(W_Wsymm @ p ** END)) :: s
    | R_Wtrans , [J_type_equality(t,t',Some p) :: s; J_type_equality(t'',t''',Some p') :: s']
      -> (* transitivity of type equality *)
	if s == s' && t' == t''
	then J_type_equality(t,t''',Some(W_Wtrans @ p ** p' ** END)) :: s
	else raise InternalError
    | _ -> raise InternalError
  end
