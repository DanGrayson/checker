(** Declaration of toplevel commands. *)

open Error
open Variables
open Typesystem

type command' =
  | Axiom of (int list) option * identifier * judgment
  | CheckLF of expr
  | CheckWitness of judgment
  | CheckLFtype of judgment
  | CheckTS of expr
  | UVariable of (string marked) list * (expr * expr) list
  | TVariable of (string marked) list
  | OVariable of (string marked) list * expr
  | Alpha of expr * expr
  | Theorem of (position * string * expr * judgment)
  | CheckUniverses
  | Show of int option
  | Back of int
  | BackTo of int
  | Include of string
  | Clear
  | SyntaxError
  | Mode of string
  | End

type command = position * command'
