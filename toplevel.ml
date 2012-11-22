(** Declaration of toplevel commands *)

open Typesystem
type command' = 
  | UPrint of uExpr
  | TPrint of expr
  | OPrint of expr
  | LFTPrint of expr
  | LFOPrint of expr
  | UCheck of uExpr
  | TCheck of expr
  | OCheck of expr
  | UVariable of string list * (uExpr * uExpr) list
  | TVariable of string list
  | UAlpha of uExpr * uExpr
  | TAlpha of expr * expr
  | OAlpha of expr * expr
  | Type of expr
  | Definition of definition
  | CheckUniverses
  | Show
  | End

type command = Error.position * command'
