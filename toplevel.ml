(** Declaration of toplevel commands. *)

open Typesystem
type command' = 
  | UPrint of expr
  | TPrint of expr
  | OPrint of expr
  | UCheck of expr
  | TCheck of expr
  | OCheck of expr
  | UVariable of string list * (expr * expr) list
  | Variable of string list
  | UAlpha of expr * expr
  | TAlpha of expr * expr
  | OAlpha of expr * expr
  | Type of expr
  | Definition of definition
  | CheckUniverses
  | Show
  | End

type command = Error.position * command'
