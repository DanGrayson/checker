(** Declaration of toplevel commands. *)

open Error
open Variables
open Typesystem

type command' =
  | Axiom of (int list) option * var * lf_type
  | CheckLF of lf_expr
  | CheckWitness of lf_type
  | CheckLFtype of lf_type
  | CheckTS of lf_expr
  | UVariable of string list * (lf_expr * lf_expr) list
  | TVariable of string list
  | OVariable of string list * lf_expr
  | Alpha of lf_expr * lf_expr
  | Theorem of (position * string * lf_expr * lf_type)
  | CheckUniverses
  | Show of int option
  | Back of int
  | BackTo of int
  | Include of string
  | Clear
  | SyntaxError
  | End

type command = Error.position * command'
