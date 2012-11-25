(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

type alpha_eq = (Typesystem.var' * Typesystem.var') list

val addalpha : Typesystem.var' -> Typesystem.var' -> alpha_eq -> alpha_eq

val testalpha' : 'a -> 'a -> ('a * 'a) list -> bool

val testalpha :
  Typesystem.expr ->
  Typesystem.expr ->
  (Typesystem.bare_expr * Typesystem.bare_expr) list -> bool

module UEqual :
  sig
    val uequiv :
      Typesystem.uContext -> Typesystem.expr -> Typesystem.expr -> bool
    val equiv :
      Typesystem.uContext -> Typesystem.expr -> Typesystem.expr -> bool
  end
module UEquivA :
  sig
    val uequiv :
      Typesystem.uContext -> Typesystem.expr -> Typesystem.expr -> bool
    val equiv :
      Typesystem.uContext -> Typesystem.expr -> Typesystem.expr -> bool
  end
