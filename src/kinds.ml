(** The various kinds of judgments. *)

(* Expressions are classified by their judgment, and judgments are classified by their kind. *)

include Judgments

type kind =
  | K_ulevel
  | K_expression
  | K_primitive_judgment
  | K_judgment
  | K_witnessed_judgment
  | K_Pi of identifier * judgment * kind

(*
  Local Variables:
  compile-command: "make -C .. src/kinds.cmo "
  End:
 *)
