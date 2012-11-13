open Typesystem
type command = 
  | Print_o of oExpr
  | Print_u of uLevel
  | Print_t of tExpr
  | Type of oExpr
  | Definition of definition
  | Declaration of declaration
