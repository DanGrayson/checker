(* coding: latin-1 *)

(**

Type system TS

@author Dan Grayson

    *)

(**

This file encodes the type system TS developed in {i A universe polymorphic
type system}, by Vladimir Voevodsky, the version dated October, 2012.

  *)

(** Object variable. *)
type oVar = OVar of string

(** Type variable. *)
type tVar = TVar of string

(** Universe variable. *)
type uVar = UVar of string

(** A u-level expression, M, is constructed inductively as: n, v, M+n, or
    max(M,M'), where v is a universe variable and n is a natural number. *)
type uLevel =
  | Uint of int
	(** Here 0 denotes the smallest universe, 1 is its successor, and so on.
	    The smallest universe is the one that [pt] lives in. *)
  | Uvariable of uVar
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
  | ULevel of uLevel
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
  | OTBinding of oVar * tExpr

(** [ooBinding] is the type of pairs (x,y) where x is an o-variable and y is an o-expression.  The
 variable [x] is thereby considered bound within [y]. *)
and ooBinding =
  | OOBinding of oVar * oExpr

(** [tExpr] is the type of T-expressions. *)
and tExpr =
  (* TS0 *)
  | Tvariable of tVar
  | U of uLevel
	(** [U]; a u-level expression, as a type *)
  | El of oExpr
	(** [El]; converts an object term into the corresponding type term *)
  | Product of tExpr * otBinding
	(** [Product(T,Bd(x,T')) <--> \[Pi;x\](T,T')] *)
    (* TS1 *)
  | Sigma of tExpr * otBinding
	(** [Sigma(T,Bd(x,T')) <--> \[Sigma;x\](T,T')] *)
    (* TS2 *)
  | PPt
      (** [Pt]; the unit type *)
    (* TS3 *)
  | Tcoprod of tExpr * tExpr
  | Tcoprod2 of tExpr * tExpr * otBinding * otBinding * oExpr

(** [oExpr] is the type of o-expressions. *)
and oExpr =
    (* TS0 *)
  | Ovariable of oVar
	(** An o-variable. *)
  | Uu of uLevel
	(** [u]; universe as an object; converted to its type [U] by [El] *)
  | Jj of uLevel * uLevel
	(** [j]; U -> U' *)
  | Ev of oExpr * oExpr * otBinding
	(** [Ev(f,o,Bd(x,T)) <--> \[ev;x\](f,o,T)]

	    Application of the function [f] to the argument [o].

	    Here [T], with the type of [o] replacing [x], gives the type of the result. *)
  | Lambda of tExpr * ooBinding
	(** [Lambda(T,Bd(x,o)) <--> \[lambda;x\](T,o)] *)
  | Forall of uLevel * uLevel * oExpr * ooBinding
	(** [Forall(M,M',o,Bd(x,o')) <--> \[forall;x\]([M],[M'],o,o')]

	    [Forall] is the object term corresponding to [Product].
	    The type of the term is given by the max of the two u-levels. *)
	(* TS1 *)
  | Pair of oExpr * oExpr * otBinding
	(** [Pair(a,b,Bd(x,T)) <--> \[pair;x\](a,b,T)]
									 
	    An instance of [Sigma]. *)
  | Pr1 of tExpr * otBinding * oExpr
	(** [Pr1(T,Bd(x,T'),o) <--> \[pr1;x\](T,T',o)] *)
  | Pr2 of tExpr * otBinding * oExpr
	(** [Pr2(T,Bd(x,T'),o) <--> \[pr2;x\](T,T',o)] *)
  | Total of uLevel * uLevel * oExpr * ooBinding
	(** [Total] is the object term corresponding to [Sigma] above *)
	(* TS2 *)
  | Pt
      (** [Pt <--> \[pt\]()]

	  [Pt] is the object corresponding to the type [PPt]. *)

  | Ptr of oExpr * otBinding
	(** [Ptr(o,Bd(x,T)) <--> \[pt_r;x\](o,T)]

	    [Ptr] is the eliminator for [Pt]. *)
  | Tt
      (** [Tt <--> \[tt\]()]
	  
	  [Tt] is the unique instance of the unit type [PPt]. *)
      (* TS3 *)
  | Ocoprod of uLevel * uLevel * oExpr * oExpr
	(** The type of the term is given by the [max] of the two u-levels. *)
  | Oii1 of tExpr * tExpr * oExpr
	(** The type of a term [Oii1(T,T',o)] is [Tcoprod(T,T')]; here [o] has type [T] *)
  | Oii2 of tExpr * tExpr * oExpr
	(** The type of a term [Oii2(T,T',o)] is [Tcoprod(T,T')]; here [o] has type [T'] *)
  | Osum of tExpr * tExpr * oExpr * oExpr * oExpr * otBinding
	(** The type of a term [Osum(T,T',s,s',o,Bd(x,S))] is [S], with [x] replaced by [o]. *)

type typingContext = (oVar * tExpr) list
	(** context; [Gamma]; to be thought of as a function from variables to T-expressions *)

let emptyContext : typingContext = []

(*
 For emacs:
 Local Variables:
  compile-command: "make typesystem.cmo doc "
  comment-column: 70
 End:
*)
