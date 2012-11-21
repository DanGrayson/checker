(** In this file, we implement definitional equality. *)

val uequal : Typesystem.uExpr -> Typesystem.uExpr -> bool
val tequal : Typesystem.expr -> Typesystem.expr -> bool
val oequal : Typesystem.expr -> Typesystem.expr -> bool
