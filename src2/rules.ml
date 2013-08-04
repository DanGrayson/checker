(** Inference rules. *) (* -*- fill-column: 122 -*- *)

open Error
open Expressions
open Substitute
open Relative

type rule_name =

  R_Empty | R_Abstr | R_TypeVar | R_Parm | R_Equal | R_equal | R_Refl | R_Symm | R_Trans| R_refl | R_symm | R_trans |
  R_Univ | R_El | R_Eleq | R_Pi | R_conv | R_lambda | R_Drop | R_ev

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
    | R_TypeVar, [s] -> J(J_istype,[]) :: s
    | R_Parm, [J(J_istype,[t]) :: s] -> J(J_hastype,[t]) :: s
    | R_conv, [J(J_type_equality,[t;t';p]) :: s; J(J_hastype,[_t;o]) :: _s] 
      when s == _s && t == _t -> 
	J(J_hastype,[t';O_conv @ o ** p ** END]) :: s
    | R_Equal, [J(J_istype,[t]) :: s; J(J_istype,[t']) :: _s]
      when s == _s -> 
	J(J_type_equality,[t;t']) :: s
    | R_equal, [J(J_hastype,[t;o]) :: s; J(J_hastype,[_t;o']) :: _s]
      when s == _s && t == _t -> 
	J(J_object_equality,[t;o;o']) :: s
    | R_Refl, [J(J_istype,[t]) :: s; J(J_istype,[t']) :: _s]
      when s == _s && t = t' -> 
	J(J_type_equality,[t;t';W_Refl @ END]) :: s
    | R_Symm, [J(J_type_equality,[t;t';p]) :: s] -> 
	J(J_type_equality,[t';t;W_Symm @ p ** END]) :: s
    | R_Trans , [J(J_type_equality,[t;t';p]) :: s; J(J_type_equality,[_t';t'';p']) :: _s]
      when s == _s && t' == _t' -> 
	J(J_type_equality,[t;t'';W_Trans @ p ** p' ** END]) :: s
    | R_refl, [J(J_hastype,[t;o]) :: s; J(J_hastype,[_t;o']) :: _s]
      when s == _s && t == _t && o = o' -> 
	J(J_object_equality,[t;o;o';W_refl @ END]) :: s
    | R_symm, [J(J_object_equality,[t;o;o';p]) :: s] -> 
	J(J_object_equality,[t;o;o';W_symm @ p ** END]) :: s
    | R_trans, [J(J_object_equality,[t;o;o';p]) :: s; J(J_object_equality,[t';_o';o'';p']) :: _s] 
      when s == _s && o' == _o' -> 
	J(J_object_equality,[t;o;o'';W_trans @ p ** p' ** END]) :: s
    | R_Univ, [s] -> J(J_istype,[T_U @ END]) :: s
    | R_El, [J(J_hastype,[BASIC(T_U,END);o]) :: s] -> J(J_istype,[T_El @ o ** END]) :: s
    | R_Eleq, [J(J_object_equality,[BASIC(T_U,END);o;o';p]) :: s] -> 
	J(J_type_equality,[T_El @ o ** END; T_El @ o' ** END; W_Eleq @ p ** END]) :: s
    | R_Pi, [J(J_istype,[u]) :: J(J_hastype,[t]) :: s] -> 
        J(J_istype,[T_Pi @ t ** u **. END]) :: s
    | R_lambda, [J(J_hastype,[u;o]) :: J(J_hastype,[t]) :: s] -> 
        J(J_hastype,[T_Pi @ t ** u **. END; O_lambda @ o **. END]) :: s
    | R_ev, [J(J_hastype,[t;x]) :: s; J(J_hastype,[BASIC(T_Pi,ARG(0,_t,ARG(1,u,END)));f]) :: _s]
        when t == _t && s == _s ->
	  let u' = subst_expr x u in
	  J(J_hastype,[u';O_ev @ f ** x ** END]) :: s
    | _ -> raise InternalError
  end
