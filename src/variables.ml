(** Variables. *)

open Error

module Identifier : 
    sig
      type identifier
      val id : string -> identifier
      val idtostring : identifier -> string
      type t = identifier
      val compare : t -> t -> int
      val isid : t -> bool
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
    let isid = function _,Object -> true | _,Witness -> false
    let id_to_name = function name,_ -> name
  end

include Identifier

type var =
  | Var of identifier
  | Rel of int			(* deBruijn index, starting with 0 *)

let var_to_name = function
  | Var i -> id_to_name i
  | Rel _ -> raise Internal

let vartostring = function
  | Var x -> idtostring x
  | Rel i -> string_of_int i ^ "^"	(* raw form *)

let isunused v = 			(* deprecated *)
  match v with
  | Var x -> id_to_name x = "_"
  | Rel _ -> raise Internal

(*
  Local Variables:
  compile-command: "make -C .. src/variables.cmo "
  End:
 *)
