(** Variables. *)

type var =
  | Rel of int			(* deBruijn index, starting with 0 *)

let vartostring = function
  | Rel i -> string_of_int i ^ "^"	(* raw form *)

(*
  Local Variables:
  compile-command: "make -C .. src/variables.cmo "
  End:
 *)
