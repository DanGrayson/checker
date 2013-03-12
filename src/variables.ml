(** Variables. *)

open Error


module Identifier : 
    sig
      type identifier
      val id : string -> identifier
      val idw : string -> identifier
      val idtostring : identifier -> string
      type t = identifier
      val compare : t -> t -> int
      val isid : t -> bool
      val isidw : t -> bool
      val id_to_name : t -> string
    end 
    =
  struct
    type flavor = Object | Witness
    type identifier = string * flavor
    type t = identifier
    let compare : t -> t -> int = Pervasives.compare
    let idtostring = function
      | name, Object -> name
      | name, Witness -> name ^ "$"
    let id name = name, Object
    let idw name = name, Witness
    let isid = function _,Object -> true | _,Witness -> false
    let isidw = function _,Object -> false | _,Witness -> true
    let id_to_name = function name,_ -> name
  end

include Identifier

let base_id v = 
  assert (isidw v);
  id (id_to_name v)

let witness_id v = 
  assert (isid v);
  idw (id_to_name v)

let is_witness_pair i j = isid i && isidw j && id_to_name i = id_to_name j

type var =
  | Var of identifier
  | VarRel of int			(* deBruijn index, starting with 0 *)

let var_to_name = function
  | Var i -> id_to_name i
  | VarRel _ -> raise Internal

let vartostring = function
  | Var x -> idtostring x
  | VarRel i -> string_of_int i ^ "^"	(* raw form *)

let is_base_var = function
  | Var x -> isid x
  | VarRel i -> i mod 2 = 1

let is_witness_var = function
  | Var x -> isidw x
  | VarRel i -> i mod 2 = 0

let base_var = function			(* deprecated *)
  | Var x -> Var (base_id x)
  | VarRel i -> if i mod 2 = 0 then VarRel (i+1) else raise Internal

let witness_var = function		(* deprecated *)
  | Var x -> Var (witness_id x)
  | VarRel i -> if i mod 2 = 1 then VarRel (i-1) else raise Internal

let isunused v = 			(* deprecated *)
  match v with
  | Var x -> id_to_name x = "_"
  | VarRel _ -> raise Internal

(*
  Local Variables:
  compile-command: "make -C .. src/variables.cmo "
  End:
 *)
