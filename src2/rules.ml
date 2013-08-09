(** Inference rules. *) (* -*- fill-column: 122 -*- *)

open Error
open Expressions
open Substitute
open Relative

type rule_name =

  R_Empty | R_Abstr | R_TypeVar | R_Parm | R_Equal | R_equal | R_Refl | R_Symm | R_Trans| R_refl | R_symm | R_trans |
  R_Univ | R_El | R_Eleq | R_Pi | R_conv | R_lambda | R_Drop | R_ev | R_beta | R_Id | R_Idrefl | R_IdRecursion

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
    | R_TypeVar, [s] -> J_Basic(J_istype,[]) :: s
    | R_Parm, [J_Basic(J_istype,[t]) :: s] -> J_Basic(J_hastype,[t]) :: s
    | R_conv, [J_Basic(J_type_equality,[t;t';p]) :: s; J_Basic(J_hastype,[_t;o]) :: _s] 
      when s == _s && t == _t -> 
	J_Basic(J_hastype,[t';O_conv @ o ** p ** END]) :: s
    | R_Equal, [J_Basic(J_istype,[t]) :: s; J_Basic(J_istype,[t']) :: _s]
      when s == _s -> 
	J_Basic(J_type_equality,[t;t']) :: s
    | R_equal, [J_Basic(J_hastype,[t;o]) :: s; J_Basic(J_hastype,[_t;o']) :: _s]
      when s == _s && t == _t -> 
	J_Basic(J_object_equality,[t;o;o']) :: s
    | R_Refl, [J_Basic(J_istype,[t]) :: s; J_Basic(J_istype,[t']) :: _s]
      when s == _s && expr_equality t t' -> 
	J_Basic(J_type_equality,[t;t';W_Refl @ END]) :: s
    | R_Symm, [J_Basic(J_type_equality,[t;t';p]) :: s] -> 
	J_Basic(J_type_equality,[t';t;W_Symm @ p ** END]) :: s
    | R_Trans , [J_Basic(J_type_equality,[t;t';p]) :: s; J_Basic(J_type_equality,[_t';t'';p']) :: _s]
      when s == _s && t' == _t' -> 
	J_Basic(J_type_equality,[t;t'';W_Trans @ p ** p' ** END]) :: s
    | R_refl, [J_Basic(J_hastype,[t;o]) :: s; J_Basic(J_hastype,[_t;o']) :: _s]
      when s == _s && t == _t && expr_equality o o' -> 
	J_Basic(J_object_equality,[t;o;o';W_refl @ END]) :: s
    | R_symm, [J_Basic(J_object_equality,[t;o;o';p]) :: s] -> 
	J_Basic(J_object_equality,[t;o;o';W_symm @ p ** END]) :: s
    | R_trans, [J_Basic(J_object_equality,[t;o;o';p]) :: s; J_Basic(J_object_equality,[t';_o';o'';p']) :: _s] 
      when s == _s && o' == _o' -> 
	J_Basic(J_object_equality,[t;o;o'';W_trans @ p ** p' ** END]) :: s
    | R_Univ, [s] -> J_Basic(J_istype,[T_U @ END]) :: s
    | R_El, [J_Basic(J_hastype,[BASIC(T_U,END);o]) :: s] -> J_Basic(J_istype,[T_El @ o ** END]) :: s
    | R_Eleq, [J_Basic(J_object_equality,[BASIC(T_U,END);o;o';p]) :: s] -> 
	J_Basic(J_type_equality,[T_El @ o ** END; T_El @ o' ** END; W_Eleq @ p ** END]) :: s
    | R_Pi, [J_Basic(J_istype,[u]) :: J_Basic(J_hastype,[t]) :: s] -> 
        J_Basic(J_istype,[T_Pi @ t ** u **. END]) :: s
    | R_lambda, [J_Basic(J_hastype,[u;o]) :: J_Basic(J_hastype,[t]) :: s] -> 
        J_Basic(J_hastype,[T_Pi @ t ** u **. END; O_lambda @ o **. END]) :: s
    | R_ev, [J_Basic(J_hastype,[t;x]) :: s; J_Basic(J_hastype,[BASIC(T_Pi,ARG(0,_t,ARG(1,u,END)));f]) :: _s]
        when t == _t && s == _s ->
	  let u' = subst_expr x u in
	  J_Basic(J_hastype,[u';O_ev @ f ** x ** END]) :: s
    | R_beta, [J_Basic(J_hastype,[t;x]) :: s ; J_Basic(J_hastype,[u;o]) :: J_Basic(J_hastype,[_t]) :: _s]
      when s == _s && t == _t ->
	let u' = subst_expr x u in
	let o' = subst_expr x o in
	let f = O_lambda @ o **. END in
	J_Basic(J_object_equality,[u'; O_ev @ f ** x ** END; o'; W_beta @ t ** u **. END]) :: s	
    | R_Id, [J_Basic(J_hastype,[t;o]) :: s; J_Basic(J_hastype,[_t;o']) :: _s]
      when s == _s && t == _t -> 
	J_Basic(J_istype,[T_Id @ t ** o ** o' ** END]) :: s
    | R_Idrefl, [J_Basic(J_hastype,[t;o]) :: s] ->
	J_Basic(J_hastype,[T_Id @ t ** o ** o ** END;O_refl @ END]) :: s
    | R_IdRecursion,
      [

       (* { ⊢ i:Id[T,a,b] } *)
       J_Basic(J_hastype,[BASIC(T_Id,ARG(0,t,ARG(0,_a,ARG(0,b,END))));i]) :: r;

       (* { ⊢ q : S[a,@refl[T,a]] } *)
       J_Basic(J_hastype,[s0;q]) :: _r;

       (* { x:T, e:Id[T,a,x] ⊢ S Type } *)
       J_Pi(
         J_Basic(J_hastype,[__t]),
         J_Pi(
           J_Basic(J_hastype,[BASIC(T_Id,ARG(0,_t,ARG(0,a,ARG(0,BASIC(Var(Rel 0),END),END))))]),
           J_Basic(J_istype,[s]))) :: __r
     ] 
       when r == _r && r == __r && t == _t && t == __t
	   && expr_equality s0 (subst_expr_l [| BASIC(O_refl,END) ; a |] s)
      ->

       (* @J[T,a,b,q,i,S] : S[b,i] *)
       J_Basic(J_hastype,
	       [ subst_expr_l [| i ; b |] s ; 
		 BASIC(O_J,ARG(0,t,ARG(0,a,ARG(0,b,ARG(0,q,ARG(0,i,ARG(2,s,END))))))) ]) :: r

    | _ -> raise InternalError
  end
