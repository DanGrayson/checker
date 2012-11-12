open Typesystem
type command = 
    Print of expr
  | Check of expr
  | Type of oExpr
  | Subst of expr * oExpr * oVar
  | Derivation of derivation

