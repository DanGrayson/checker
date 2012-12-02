(** Reduction of expressions. *)

open Typesystem

let beta1 (f:ts_expr) (o:ts_expr) : ts_expr = 
  match unmark f with
  | APPLY(O O_lambda, [CAN t; LAMBDA(x,CAN b)]) ->
      Substitute.subst (x,CAN o) b
  | _ -> raise Error.Internal
