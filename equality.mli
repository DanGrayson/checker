(** In this file, we implement definitional equality. *)

val uequal : Typesystem.uExpr -> Typesystem.uExpr -> bool
val tequal : Typesystem.tExpr -> Typesystem.tExpr -> bool
val oequal : Typesystem.oExpr -> Typesystem.oExpr -> bool
