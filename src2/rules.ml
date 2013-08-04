(** Inference rules. *) (* -*- fill-column: 122 -*- *)

open Error
open Expressions

type rule_name =

  R_Empty | R_Abstr | R_TypeVar | R_Parm | R_Equal | R_equal | R_Refl | R_Symm | R_Trans| R_refl | R_symm | R_trans |
  R_Univ | R_El | R_Eleq | R_Pi | R_conv | R_lambda

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
    | R_conv, [J_type_equality(t,t',Some(p)) :: s; J_hastype(t'',Some(o)) :: s'] -> (* convert an object to an equal type *)
	if s == s' && t == t''
	then J_hastype(t',Some(O_conv @ o ** p ** END)) :: s
	else raise InternalError
    | R_Equal, [J_istype(Some t) :: s; J_istype(Some t') :: s'] -> (* assume two types are equal *)
	if s == s' 
	then J_type_equality(t,t',None) :: s
	else raise InternalError
    | R_equal, [J_hastype(t,Some o) :: s; J_hastype(t',Some o') :: s'] -> (* assume two objects are equal *)
	if s == s' && t == t'
	then J_object_equality(t,o,o',None) :: s
	else raise InternalError
    | R_Refl, [J_istype(Some t) :: s; J_istype(Some t') :: s'] -> (* record that two types are equal *)
	if s == s' && t = t'
	then J_type_equality(t,t',Some(W_Refl @ END)) :: s
	else raise InternalError
    | R_Symm, [J_type_equality(t,t',Some p) :: s] -> (* symmetry of type equality *)
	J_type_equality(t',t,Some(W_Symm @ p ** END)) :: s
    | R_Trans , [J_type_equality(t,t',Some p) :: s; J_type_equality(t'',t''',Some p') :: s']
      -> (* transitivity of type equality *)
	if s == s' && t' == t''
	then J_type_equality(t,t''',Some(W_Trans @ p ** p' ** END)) :: s
	else raise InternalError
    | R_refl, [J_hastype(t,Some o) :: s; J_hastype(t',Some o') :: s'] -> (* record that two objects are equal *)
	if s == s' && t == t' && o = o'
	then J_object_equality(t,o,o',Some(W_refl @ END)) :: s
	else raise InternalError
    | R_symm, [J_object_equality(t,o,o',Some p) :: s] -> (* symmetry of object equality *)
	J_object_equality(t,o,o',Some(W_symm @ p ** END)) :: s
    | R_trans, [J_object_equality(t,o,o',Some p) :: s; J_object_equality(t',o'',o''',Some p') :: s']
      -> (* transitivity of object equality *)
	if s == s' && o' == o''
	then J_object_equality(t,o,o''',Some(W_trans @ p ** p' ** END)) :: s
	else raise InternalError
    | R_Univ, [s] -> (* the universe is a type *)
	J_istype(Some(T_U @ END)) :: s
    | R_El, [J_hastype(BASIC(T_U,END), Some(o)) :: s] -> (* El[o] is a type if o is an element of the universe *)
	J_istype(Some(T_El @ o ** END)) :: s
    | R_Eleq, [J_object_equality(BASIC(T_U,END), o, o', Some(p)) :: s] -> (* El[o]=El[o'] if o=o' *)
	J_type_equality(T_El @ o ** END,T_El @ o' ** END, Some(W_Eleq @ p ** END)) :: s
    | R_Pi, [J_istype(Some(u)) :: J_hastype(t,None) :: s] -> (* Pi[T,.U] is a type *)
        J_istype(Some(T_Pi @ t ** u **. END)) :: s
    | R_lambda, [J_hastype(u,Some(o)) :: J_hastype(t,None) :: s] -> (* lambda[.o] has type Pi[T,.U] *)
        J_hastype(T_Pi @ t ** u **. END, Some(O_lambda @ o **. END)) :: s
    | _ -> raise InternalError
  end
