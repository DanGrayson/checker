  (* 

     This file encodes the type system TS developed in A universe polymorphic
     type system, by Vladimir Voevodsky, the version dated Oct 2012.

   *)

type oVar = string					(* object variable *)
type tVar = string					(* type variable *)
type uVar = string					(* universe variable *)

type var =							 (* variable *)
  | Ovar of oVar
  | Tvar of tVar
  | Uvar of uVar

type uLevel =					       (* u-level expression *)
  | Uint of int					       (* 0 is Prop *)
  | Uplus of uLevel * int
  | Umax of uLevel * uLevel

type uContext =						 (* universe context *)
    uVar list * (uLevel * uLevel) (* equation *) list

type expr =
  | Uexpr of uLevel
  | Texpr of tExpr						   (* type *)
  | Oexpr of oExpr						   (* object *)
and tExpr =
  | Tvariable of tVar
  | UU of uLevel						      (* U; universe as a type *)
  | El of oExpr							      (* (Proof) *)
  | Product of oVar * tExpr * tExpr
and oExpr =
  | Ovariable of oVar
  | Uu of uLevel						   (* u; universe as an object; converted to its type by El *)
  | Jj of uLevel * uLevel					   (* j; U -> U' *)
  | Ev of oVar * oExpr * oExpr * tExpr		(* ev (evaluation; apply; App)
						   The objects don't involve the variable.
						   The type expression gives the target type and may involve the variable 
						   the variable is to be replaced by the second object.
						 *)
  | Lambda of oVar * tExpr * oExpr				    (* lambda; 
								       the object expression my involve the variable 
								     *)
  | Forall of oVar * uLevel * uLevel * oExpr * oExpr		     (* forall;
									The first expression does not involve the variable.
									The second expression may involve the variable.
									The type of the result is given by the max of the two u-levels.
								      *)

type typingContext = (oVar * tExpr) list			      (* context; Gamma; to be thought of as a function *)

let emptyContext : typingContext = []



(*
 Local Variables:
   comment-column: 70
 End:
 *)
