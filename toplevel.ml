open Typesystem
type command = 
  | Print_o of oExpr
  | Print_u of uExpr
  | Print_t of tExpr
  | TVariable of string list
  | UVariable of string list * (uExpr * uExpr) list
  | Type of oExpr
  | Notation of notation
  | Show
  | Exit
