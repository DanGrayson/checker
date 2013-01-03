(** Declaration of toplevel commands. *)

open Error
open Variables
open Typesystem

type binder_mode = Binder_mode_relative | Binder_mode_pairs

let binder_mode = ref Binder_mode_relative

type command' = 
  | Axiom of (int list) option * string * lf_type
  | CheckLF of lf_expr
  | CheckLFtype of lf_type
  | CheckTS of lf_expr
  | UVariable of string list * (lf_expr * lf_expr) list
  | Variable of string list
  | Alpha of lf_expr * lf_expr
  | Theorem of (position * string * lf_expr * lf_type)
  | CheckUniverses
  | Show of int option
  | Include of string
  | Clear
  | Mode_single
  | Mode_pairs
  | Mode_relative
  | End

type command = Error.position * command'