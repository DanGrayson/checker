(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

val uequal : Typesystem.uExpr -> Typesystem.uExpr -> bool
val tequal : Typesystem.tExpr -> Typesystem.tExpr -> bool
val oequal : Typesystem.oExpr -> Typesystem.oExpr -> bool
