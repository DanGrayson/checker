(** Tactics. *)

open Error
open Variables
open Typesystem
open Names

let add_tactic name f =
  Lfcheck.tactics := (name,f) :: !Lfcheck.tactics

(** find the first variable in the context of the right type and return it *)
let rec assumption surr env pos t =
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
      else assumption surr env pos t
  | [] -> None

(** fill in the third argument of [ev](f,x,_) using tau *)
let ev3 surr env pos t =
  raise NotImplemented

let _ = 
  add_tactic "ev3" assumption;
  add_tactic "assumption" assumption;
  add_tactic "a" assumption
