(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

type alpha_eq = (Typesystem.var' * Typesystem.var') list

val addalpha : Typesystem.var' -> Typesystem.var' -> alpha_eq -> alpha_eq

val testalpha' : 'a -> 'a -> ('a * 'a) list -> bool

val testalpha :
  Typesystem.lf_expr ->
  Typesystem.lf_expr ->
  (Typesystem.var' * Typesystem.var') list -> bool

module UEqual :
  sig
    val uequiv :
      Printer.uContext -> Typesystem.lf_expr -> Typesystem.lf_expr -> bool
    val equiv :
      Printer.uContext -> Typesystem.lf_expr -> Typesystem.lf_expr -> bool
  end
module UEquivA :
  sig
    val uequiv :
      Printer.uContext -> Typesystem.lf_expr -> Typesystem.lf_expr -> bool
    val equiv :
      Printer.uContext -> Typesystem.lf_expr -> Typesystem.lf_expr -> bool
  end
