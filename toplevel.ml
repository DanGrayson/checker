open Typesystem
type command = 
    Print of expr
  | Check of expr
  | Type of oExpr
  | Subst of expr * oExpr * oVar	(* this will become part of TS, as an abbreviation *)
  | Derivation of derivation	(* this will become part of TS, as an abbreviation *)

