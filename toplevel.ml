open Typesystem
type command = 
    Print of expr
  | Check of expr
  | Type of expr
  | Subst of expr * oExpr * oVar
