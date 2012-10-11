  (* 

     This file encodes the type system TS developed in A universe polymorphic
     type system, by Vladimir Voevodsky, the version dated Oct 2012.

   *)

type var =				(* variable *)
  | Ovar of string			(* object *)
  | Tvar of string			(* type *)
  | Uvar of string			(* universe *)

type uLevel =				(* u-level expression *)
  | Uint of int
  | Uplus of uLevel * int
  | Umax of uLevel * uLevel

type uContext =				(* universe context *)
    var (* Uvar _ *) list * (uLevel * uLevel) (* equation *) list

