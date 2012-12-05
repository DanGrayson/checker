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
  | Definition of (var * Error.position * lf_expr * lf_type) list
  | CheckUniverses
  | Show of int option
  | End

type command = Error.position * command'
