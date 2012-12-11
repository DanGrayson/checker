(** Declaration of toplevel commands. *)

open Variables
open Typesystem

type command' = 
  | AxiomTS of string * lf_expr
  | AxiomLF of string * lf_type
  | Rule of int list * string * lf_type
  | CheckLF of lf_expr
  | CheckLFtype of lf_type
  | CheckTS of lf_expr
  | UVariable of string list * (lf_expr * lf_expr) list
  | Variable of string list
  | Alpha of lf_expr * lf_expr
  | TDefinition of (string * Definitions.parm list * lf_expr * lf_expr option)
  | ODefinition of (string * Definitions.parm list * lf_expr * lf_expr * lf_expr option)
  | TeqDefinition of (string * Definitions.parm list * lf_expr * lf_expr)
  | OeqDefinition of (string * Definitions.parm list * lf_expr * lf_expr * lf_expr)
  | CheckUniverses
  | Show of int option
  | End

type command = Error.position * command'
