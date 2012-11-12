open Typesystem
type command = 
  | Print_o of oExpr
  | Print_u of uLevel
  | Print_t of tExpr
  | Type of oExpr
  | Derivation of derivation	(* this will become part of TS, as an abbreviation *)

