(** Reduction of expressions. *)

open Typesystem

let beta1 f o = match strip_pos f with
  Expr(OO OO_lambda, [t;Expr(BB x,[b])]) -> Substitute.subst [(strip_pos_var x,o)] b
| _ -> raise InternalError
