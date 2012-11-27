(** Declaration of toplevel commands. *)

open Typesystem
type command' = 
  | Print of expr
  | F_Print of lftype
  | Rule of int * string * lftype
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
