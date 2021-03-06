(** Declaration of toplevel commands. *)

open Typesystem

type command' =
  | Axiom of (int list) option * identifier * judgment
  | CheckType of judgment
  | CheckLF of expr
  | CheckTS of expr
  | UVariable of (string marked) list * (expr * expr) list
  | TVariable of (string marked) list
  | OVariable of (string marked) list * expr
  | Alpha of expr * expr
  | Theorem of (position * string option * expr * judgment)
  | CheckUniverses
  | Show of int option
  | Back of int
  | BackTo of int
  | Include of position * string
  | Clear
  | SyntaxError
  | Mode of string
  | End

type command = position * command'
