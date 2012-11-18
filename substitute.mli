(** Substitution *)

val tsubst : Typesystem.oSubs -> Typesystem.tExpr -> Typesystem.tExpr
val osubst : Typesystem.oSubs -> Typesystem.oExpr -> Typesystem.oExpr
