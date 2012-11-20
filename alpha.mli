(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

module UEqual :
  sig
    val uequiv :
      Typesystem.uContext -> Typesystem.uExpr -> Typesystem.uExpr -> bool
    val equiv :
      Typesystem.uContext -> Typesystem.expr -> Typesystem.expr -> bool
  end
module UEquivA :
  sig
    val uequiv :
      Typesystem.uContext -> Typesystem.uExpr -> Typesystem.uExpr -> bool
    val equiv :
      Typesystem.uContext -> Typesystem.expr -> Typesystem.expr -> bool
  end
