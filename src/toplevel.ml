(** Declaration of toplevel commands. *)

open Error
open Variables
open Typesystem

type command' =
  | Axiom of (int list) option * identifier * lf_type
  | CheckLF of expr
  | CheckWitness of lf_type
  | CheckLFtype of lf_type
  | CheckTS of expr
  | UVariable of (string marked) list * (expr * expr) list
  | TVariable of (string marked) list
  | OVariable of (string marked) list * expr
  | Alpha of expr * expr
  | Theorem of (position * string * expr * lf_type)
  | CheckUniverses
  | Show of int option
  | Back of int
  | BackTo of int
  | Include of string
  | Clear
  | SyntaxError
  | Mode of string
  | End

type command = Error.position * command'
