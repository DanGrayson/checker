(** Variables. *)

open Error

type identifier =			(* variables come in pairs, with the *_wd version being the witness twin *)
  | Id of string
  | Idw of string

module Identifier = struct
  type t = identifier
  let compare v w = match v,w with
  | Id a, Id b -> compare a b
  | Idw a, Idw b -> compare a b
  | Id a, Idw b -> let r = compare a b in if r = 0 then  1 else r
  | Idw a, Id b -> let r = compare a b in if r = 0 then -1 else r
end

let idtostring = function
  | Id name -> name
  | Idw name -> name ^ "$"

let base_id = function
  | Id name -> raise Internal
  | Idw name -> Id name

let witness_id = function
  | Id name -> Idw name
  | Idw name -> raise Internal

type var =
  | Var of identifier
  | VarRel of int			(* deBruijn index, starting with 0 *)

let vartostring = function
  | Var x -> idtostring x
  | VarRel i -> string_of_int i ^ "^"	(* raw form *)

let base_var = function			(* deprecated *)
  | Var x -> Var (base_id x)
  | VarRel i -> if i mod 2 = 0 then VarRel (i+1) else raise Internal

let witness_var = function		(* deprecated *)
  | Var x -> Var (witness_id x)
  | VarRel i -> if i mod 2 = 1 then VarRel (i-1) else raise Internal

exception GensymCounterOverflow

let isunused v = 			(* deprecated *)
  match v with
  | Var (Id "_" | Idw "_") -> true
  | Var _ -> false
  | VarRel _ -> raise Internal

(*
  Local Variables:
  compile-command: "make -C .. src/variables.cmo "
  End:
 *)
