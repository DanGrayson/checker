open Typesystem
type command = 
  | Print_o of oExpr
  | Print_u of uLevel
  | Print_t of tExpr
  | TVariable of string list
  | UVariable of string list * (uLevel * uLevel) list
  | Type of oExpr
  | Notation of notation
  | Show
  | Exit
