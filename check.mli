exception TypeCheckingFailure of Typesystem.position * string
exception TypeCheckingFailure2 of Typesystem.position * string * Typesystem.position * string
exception TypeCheckingFailure3 of Typesystem.position * string * Typesystem.position * string * Typesystem.position * string
val ucheck : Typesystem.environment_type -> Typesystem.uExpr -> unit
val tcheck : Typesystem.environment_type -> Typesystem.tExpr -> unit
val ocheck : Typesystem.environment_type -> Typesystem.oExpr -> unit
val ucheck_okay : Typesystem.environment_type -> Typesystem.uExpr -> bool
val tcheck_okay : Typesystem.environment_type -> Typesystem.tExpr -> bool
val ocheck_okay : Typesystem.environment_type -> Typesystem.oExpr -> bool
