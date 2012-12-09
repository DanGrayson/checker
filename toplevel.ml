(** Declaration of toplevel commands. *)

open Variables
open Typesystem

type command' = 
  | AxiomTS of string * atomic_expr
  | AxiomLF of string * lf_type
  | Rule of int list * string * lf_type
  | CheckLF of lf_expr
  | CheckLFtype of lf_type
  | CheckTS of atomic_expr
  | UVariable of string list * (atomic_expr * atomic_expr) list
  | Variable of string list
  | Alpha of atomic_expr * atomic_expr
  | TDefinition of (string * Definitions.parm list * atomic_expr * lf_expr option)
  | ODefinition of (string * Definitions.parm list * atomic_expr * atomic_expr * lf_expr option)
  | TeqDefinition of (string * Definitions.parm list * atomic_expr * atomic_expr)
  | OeqDefinition of (string * Definitions.parm list * atomic_expr * atomic_expr * atomic_expr)
  | CheckUniverses
  | Show of int option
  | End

type command = Error.position * command'
