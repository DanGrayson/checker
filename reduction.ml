(** Reduction of expressions. *)

open Typesystem

let beta1 f o = match strip_pos f with
  APPLY(OO OO_lambda, [t;APPLY(LAMBDA x,[b])]) -> Substitute.subst [(strip_pos_var x,o)] b
| _ -> raise Error.Internal
