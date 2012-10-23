  (* 

     This file encodes the type system TS developed in A universe polymorphic
     type system, by Vladimir Voevodsky, the version dated Oct 2012.

   *)

type oVar = Ovar of string					(* object variable *)
type tVar = Tvar of string					(* type variable *)
type uVar = Uvar of string					(* universe variable *)

type uLevel =					       (* u-level expression M *)
  | Uint of int					       (* 0 is Prop *)
  | Uvar of uVar
  | Uplus of uLevel * int
  | Umax of uLevel * uLevel

type uContext =						 (* universe context *)
    uVar list * (uLevel * uLevel) (* equation *) list

type expr =
    (* TS0 *)
  | Uexpr of uLevel					      (* Uexpr(M) <--> [M] *)
  | Texpr of tExpr						   (* type term *)
  | Oexpr of oExpr						   (* object term *)
    (* TS1 *)
    (* TS2 *)
and tExpr =
    (* TS0 *)
  | Tvariable of tVar
  | UU of uLevel						      (* U; universe as a type *)
  | El of oExpr							      (* El(o) <---> [El](o)
									 converts an object term into the corresponding type term
								       *)
  | Product of oVar * tExpr * tExpr					(* Product(x,T,T') <--> [Pi;x](T,T') 
									   T does not contain x
									 *)
    (* TS1 *)
  | Sigma of oVar * tExpr * tExpr					(* Sigma(x,T,T') <--> [Sigma;x](T,T') 
									   T does not contain x
									 *)
    (* TS2 *)
  | PPt								      (* PPt <--> [Pt]
									 the unit type *)
and oExpr =
    (* TS0 *)
  | Ovariable of oVar
  | Uu of uLevel						   (* u; universe as an object; converted to its type by El *)
  | Jj of uLevel * uLevel					   (* j; U -> U' *)
  | Ev of oVar * oExpr * oExpr * tExpr		(* Ev(x,f,o,T) <--> [ev;x](f,o,T)
						   Here f and o don't involve x, what's intended is the application of
						   the function f to the argument o, and T, with the type of o replacing x,
						   gives the type of the result.
						 *)
  | Lambda of oVar * tExpr * oExpr				    (* Lambda(x,T,o) <--> [lambda;x](T,o)
								       the object expression may involve the variable 
								     *)
  | Forall of oVar * uLevel * uLevel * oExpr * oExpr		     (* Forall(x,M,M',o,o') <--> [forall;x]([M],[M'],o,o')
									This is the object term corresponding to Product(x,T,T').
									The first expression does not involve the variable.
									The second expression may involve the variable.
									The type of the result is given by the max of the two u-levels.
								      *)
    (* TS1 *)
  | Pair of oVar * oExpr * oExpr * tExpr			      (* Pair(x,,,) <--> [pair;x](,,)
									 an instance of Sigma
								       *)
  | Pr1 of oVar * tExpr * tExpr * oExpr				      (* Pr1(x,T,T',o) <--> [pr1;x](T,T',o) *)
  | Pr2 of oVar * tExpr * tExpr * oExpr				      (* Pr2(x,T,T',o) <--> [pr2;x](T,T',o) *)
  | Total of oVar * uLevel * uLevel * oExpr * oExpr                   (* the object term corresponding to Sigma above *)
    (* TS2 *)
  | Pt								      (* Pt <--> [pt]() 
									 the object corresponding to PPt
								       *)

  | Ptr of oVar * uLevel (*??*) * oExpr * tExpr		      	      (* Ptr(x,o,T) <--> [pt_r;x](o,T) 
									 the eliminator for Pt
								       *)

  | Tt								      (* Tt <--> [tt]() 
									 the unique instance of the unit type PPt
								       *)

type typingContext = (oVar * tExpr) list			      (* context; Gamma; to be thought of as a function *)

let emptyContext : typingContext = []

(*
 Local Variables:
  compile-command: "make typesystem.cmo "
  comment-column: 70
 End:
 *)
