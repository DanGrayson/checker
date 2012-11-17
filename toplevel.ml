open Typesystem
type command = 
  | UPrint of uExpr
  | TPrint of tExpr
  | OPrint of oExpr
  | UCheck of uExpr
  | TCheck of tExpr
  | OCheck of oExpr
  | UVariable of string list * (uExpr * uExpr) list
  | TVariable of string list
  | UAlpha of uExpr * uExpr
  | TAlpha of tExpr * tExpr
  | OAlpha of oExpr * oExpr
  | Type of oExpr
  | Definition of definition
  | Show
  | End
