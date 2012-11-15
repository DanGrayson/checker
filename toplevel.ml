open Typesystem
type command = 
  | OPrint of oExpr
  | UPrint of uExpr
  | TPrint of tExpr
  | TVariable of string list
  | UVariable of string list * (uExpr * uExpr) list
  | UAlpha of uExpr * uExpr
  | TAlpha of tExpr * tExpr
  | OAlpha of oExpr * oExpr
  | Type of oExpr
  | Notation of notation
  | Show
  | Exit
