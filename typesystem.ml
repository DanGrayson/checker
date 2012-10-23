  (**

     Type system TS

     @author Dan Grayson
   *)

  (**

     This file encodes the type system TS developed in A universe polymorphic
     type system, by Vladimir Voevodsky, the version dated Oct 2012.

   *)

(** Object variable. *)
type oVar = Ovar of string

(** Type variable. *)
type tVar = Tvar of string

(** Universe variable. *)
type uVar = Uvar of string

(** A u-level expression, M, is constructed inductively as: n, v, M+n, or
    max(M,M'), where v is a universe variable and n is a natural number. *)
type uLevel =
  | Uint of int
	(** Here 0 denotes the smallest universe, 1 is its successor, and so on.  
	    We may want to eliminate this variant, as there seems to be no need for a smallest universe. *)
  | Uvar of uVar
	(** A u-level variable. *)
  | Uplus of uLevel * int
	(** A pair (M,n), denoting M+n, the n-th successor of M.  Here n should be nonnegative *)
  | Umax of uLevel * uLevel
	(** A pair (M,M') denoting max(M,M'). *)

(** A universe context is a list of universe variables and a list of equations between two u-level expressions. *)
type uContext =
    uVar list * (uLevel * uLevel) list

type expr =
    (* TS0 *)
  | Uexpr of uLevel
	(** Universe term, \[M\]. *)
  | Texpr of tExpr
	(** Type term. *)
  | Oexpr of oExpr
	(** Object term. *)
    (* TS1 *)
    (* TS2 *)

(** [otBinding] is the type of pairs (x,T) where x is an o-variable and T is a type term.  The
 variable [x] is thereby considered bound within [T]. *)
and otBinding =
  | Bot of oVar * tExpr

(** [ooBinding] is the type of pairs (x,y) where x is an o-variable and y is an o-expression.  The
 variable [x] is thereby considered bound within [y]. *)
and ooBinding =
  | Boo of oVar * oExpr

(** [tExpr] is the type of T-expressions. *)
and tExpr =
  (* TS0 *)
  | Tvariable of tVar
  | U of uLevel
	(** U; a u-level expression, as a type *)
  | El of oExpr
	(** [El]; converts an object term into the corresponding type term *)
  | Product of tExpr * otBinding
	(** Product(T,Bd(x,T')) <--> \[Pi;x\](T,T') *)
    (* TS1 *)
  | Sigma of tExpr * otBinding
	(** Sigma(T,Bd(x,T')) <--> \[Sigma;x\](T,T') *)
    (* TS2 *)
  | PPt
      (** [Pt]; the unit type *)

(** [oExpr] is the type of o-expressions. *)
and oExpr =
    (* TS0 *)
  | Ovariable of oVar
	(** An o-variable. *)
  | Uu of uLevel
	(** u; universe as an object; converted to its type [U] by [El] *)
  | Jj of uLevel * uLevel
	(** j; U -> U' *)
  | Ev of oExpr * oExpr * otBinding
	(** Ev(f,o,Bd(x,T)) <--> \[ev;x\](f,o,T)
	    Application of the function [f] to the argument [o], and T, with the type of o replacing x,
	    gives the type of the result. *)
  | Lambda of oVar * tExpr * oExpr
	(** Lambda(x,T,o) <--> \[lambda;x\](T,o)
								       the object expression may involve the variable 
								     *)
  | Forall of oVar * uLevel * uLevel * oExpr * oExpr
	(** Forall(x,M,M',o,o') <--> \[forall;x\]([M],[M'],o,o')
									This is the object term corresponding to Product(x,T,T').
									The first expression does not involve the variable.
									The second expression may involve the variable.
									The type of the result is given by the max of the two u-levels.
								      *)
    (* TS1 *)
  | Pair of oExpr * oExpr * otBinding
	(** [Pair(a,b,Bd(x,T)) <--> \[pair;x\](a,b,T)]
									 
	    An instance of [Sigma]. *)
  | Pr1 of tExpr * otBinding * oExpr
	(** Pr1(T,Bd(x,T'),o) <--> \[pr1;x\](T,T',o) *)
  | Pr2 of tExpr * otBinding * oExpr
	(** Pr2(T,Bd(x,T'),o) <--> \[pr2;x\](T,T',o) *)
  | Total of uLevel * uLevel * oExpr * ooBinding
	(** the object term corresponding to [Sigma] above *)
    (* TS2 *)
  | Pt
	(** Pt <--> \[pt\]() 
									 the object corresponding to PPt
								       *)

  | Ptr of oVar * uLevel
	(**??*) * oExpr * tExpr
	(** Ptr(x,o,T) <--> \[pt_r;x\](o,T) 
									 the eliminator for Pt
								       *)

  | Tt
	(** Tt <--> \[tt\]() 
									 the unique instance of the unit type PPt
								       *)

type typingContext = (oVar * tExpr) list
	(** context; Gamma; to be thought of as a function *)

let emptyContext : typingContext = []
	(**
 Local Variables:
  compile-command: "make typesystem.cmo "
  comment-column: 70
 End:
 *)
