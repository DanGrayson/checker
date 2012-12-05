(** Tactics. *)

open Typesystem
open Names

let add_tactic name f =
  Lfcheck.tactics := (name,f) :: !Lfcheck.tactics

let rec assumption env pos t =
  match env with 
  | (v,u) :: env ->
      if Alpha.UEqual.type_equiv empty_uContext t u
      then Some(var_to_lf v)
      else assumption env pos t
  | [] -> None

let _ = 
  add_tactic "assumption" assumption;
  add_tactic "a" assumption
