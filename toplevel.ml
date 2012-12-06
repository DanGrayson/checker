(** Declaration of toplevel commands. *)

open Typesystem
type command' = 
  | AxiomTS of string * ts_expr
  | AxiomLF of string * lf_type
  | Rule of int * string * lf_type
  | CheckLF of lf_expr
  | CheckLFtype of lf_type
  | Check of ts_expr
  | UVariable of string list * (ts_expr * ts_expr) list
  | Variable of string list
  | Alpha of ts_expr * ts_expr
  | TDefinition of (string * Definitions.parm list * ts_expr * lf_expr option)
  | ODefinition of (string * Definitions.parm list * ts_expr * ts_expr)
  | TeqDefinition of (string * Definitions.parm list * ts_expr * ts_expr)
  | OeqDefinition of (string * Definitions.parm list * ts_expr * ts_expr * ts_expr)
  | CheckUniverses
  | Show of int option
  | End

type command = Error.position * command'
