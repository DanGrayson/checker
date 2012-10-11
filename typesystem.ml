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
  | Uint of int
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
  | UU of uLevel						      (* U *)
  | El of oExpr
  | Product of oVar * tExpr * tExpr
and oExpr =
  | Ovariable of oVar
  | Uu of uLevel						   (* u *)
  | Jj of uLevel * uLevel					   (* j *)
  | Ev of oVar * oExpr * oExpr * tExpr				   (* ev *)
  | Lambda of oVar * tExpr * oExpr				   (* lambda *)
  | Forall of uLevel * uLevel *	oExpr * oExpr			   (* forall *)

(*
 Local Variables:
   comment-column: 70
 End:
 *)
