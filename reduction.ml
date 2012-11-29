(** Reduction of expressions. *)

open Typesystem

let beta1 f o = match strip_pos f with
  APPLY(O O_lambda, [ATOMIC t; LAMBDA(x,ATOMIC b)]) -> Substitute.subst [(strip_pos x,o)] b
| _ -> raise Error.Internal
