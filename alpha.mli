(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

module UEqual : sig
  val uequiv : Typesystem.uContext -> Typesystem.uExpr -> Typesystem.uExpr -> bool
  val tequiv : Typesystem.uContext -> Typesystem.tExpr -> Typesystem.tExpr -> bool
  val oequiv : Typesystem.uContext -> Typesystem.oExpr -> Typesystem.oExpr -> bool
end
module UEquivA : sig
  val uequiv : Typesystem.uContext -> Typesystem.uExpr -> Typesystem.uExpr -> bool
  val tequiv : Typesystem.uContext -> Typesystem.tExpr -> Typesystem.tExpr -> bool
  val oequiv : Typesystem.uContext -> Typesystem.oExpr -> Typesystem.oExpr -> bool
end
