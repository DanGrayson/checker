(** Inference rules. *) (* -*- fill-column: 122 -*- *)

open Error
open Expressions
open Relative

type rule_name =

  R_Empty | R_Abstr | R_TypeVar | R_Parm | R_Equal | R_equal | R_Refl | R_Symm | R_Trans| R_refl | R_symm | R_trans |
  R_Univ | R_El | R_Eleq | R_Pi | R_conv | R_lambda | R_Drop

module InferenceRules :
    sig
      type statement
      val expose : statement -> judgment list
      val rule : rule_name * statement list -> statement
    end =
  struct
    type statement = judgment list
    let expose s = s
    let rule n = match n with
    | R_Empty, [] -> []
    | R_Drop, [p :: s] -> s
    | R_Abstr, [q :: p :: s] -> J_Pi(p,q) :: s
    | R_TypeVar, [s] -> J_istype(None) :: s
    | R_Parm, [J_istype(Some t) :: s] -> J_hastype(t,None) :: s
    | R_conv, [J_type_equality(t,t',Some(p)) :: s; J_hastype(_t,Some(o)) :: _s] when s == _s && t == _t -> 
	J_hastype(t',Some(O_conv @ o ** p ** END)) :: s
    | R_Equal, [J_istype(Some t) :: s; J_istype(Some t') :: _s] when s == _s -> 
	J_type_equality(t,t',None) :: s
    | R_equal, [J_hastype(t,Some o) :: s; J_hastype(_t,Some o') :: _s] when s == _s && t == _t -> 
	J_object_equality(t,o,o',None) :: s
    | R_Refl, [J_istype(Some t) :: s; J_istype(Some t') :: _s] when s == _s && t = t' -> 
	J_type_equality(t,t',Some(W_Refl @ END)) :: s
    | R_Symm, [J_type_equality(t,t',Some p) :: s] -> 
	J_type_equality(t',t,Some(W_Symm @ p ** END)) :: s
    | R_Trans , [J_type_equality(t,t',Some p) :: s; J_type_equality(t'',t''',Some p') :: _s] when s == _s && t' == t'' -> 
	J_type_equality(t,t''',Some(W_Trans @ p ** p' ** END)) :: s
    | R_refl, [J_hastype(t,Some o) :: s; J_hastype(t',Some o') :: _s] when s == _s && t == t' && o = o' -> 
	J_object_equality(t,o,o',Some(W_refl @ END)) :: s
    | R_symm, [J_object_equality(t,o,o',Some p) :: s] -> 
	J_object_equality(t,o,o',Some(W_symm @ p ** END)) :: s
    | R_trans, [J_object_equality(t,o,o',Some p) :: s; J_object_equality(t',_o',o'',Some p') :: _s] 
      when s == _s && o' == _o' -> 
	J_object_equality(t,o,o'',Some(W_trans @ p ** p' ** END)) :: s
    | R_Univ, [s] -> J_istype(Some(T_U @ END)) :: s
    | R_El, [J_hastype(BASIC(T_U,END), Some(o)) :: s] -> J_istype(Some(T_El @ o ** END)) :: s
    | R_Eleq, [J_object_equality(BASIC(T_U,END), o, o', Some(p)) :: s] -> 
	J_type_equality(T_El @ o ** END,T_El @ o' ** END, Some(W_Eleq @ p ** END)) :: s
    | R_Pi, [J_istype(Some(u)) :: J_hastype(t,None) :: s] -> 
        J_istype(Some(T_Pi @ t ** u **. END)) :: s
    | R_lambda, [J_hastype(u,Some(o)) :: J_hastype(t,None) :: s] -> 
        J_hastype(T_Pi @ t ** u **. END, Some(O_lambda @ o **. END)) :: s
    | _ -> raise InternalError
  end
