(** Declaration of toplevel commands. *)

open Typesystem
type command' = 
  | Print of expr
  | Check of expr
  | UVariable of string list * (expr * expr) list
  | Variable of string list
  | Alpha of expr * expr
  | Type of expr
  | Definition of (string * definition)
  | CheckUniverses
  | Show
  | End

type command = Error.position * command'
