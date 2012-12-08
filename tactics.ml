(** Tactics. *)

open Variables
open Typesystem
open Names

let add_tactic name f =
  Lfcheck.tactics := (name,f) :: !Lfcheck.tactics

let rec assumption env pos t =
  match env with 
  | (v,u) :: env ->
      if 
	try
	  Lfcheck.type_equivalence env t u;
	  true
	with 
	| TypeCheckingFailure _
	| TypeCheckingFailure2 _
	| TypeCheckingFailure3 _ -> false
      then Some(var_to_lf v)
      else assumption env pos t
  | [] -> None

let _ = 
  add_tactic "assumption" assumption;
  add_tactic "a" assumption
