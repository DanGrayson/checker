(** Reduction of expressions. *)

open Typesystem

let beta1 (f:ts_expr) (o:ts_expr) : ts_expr = 
  match strip_pos f with
  | APPLY(O O_lambda, [ATOMIC t; LAMBDA(x,ATOMIC b)]) ->
      Substitute.subst (strip_pos x,ATOMIC o) b
  | _ -> raise Error.Internal
