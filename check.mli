(** In this file we do typechecking.  

    For a t-expression, this just amounts to being well-formed, since types
    have no type.  For an o-expression, it's a meta-theorem that the type turns
    out to equal the result that the function tau yields.  The body of a
    definition is checked in its local context, as a t-expression or as an
    o-expression; it's a meta-theorem that later substitution preserves types,
    so unfolding of o-definitions embedded in other expressions is not needed
    at the point they are encounted, as the type of the result obtained by
    unfolding is more easily obtained by substitution; unfolding of
    t-definitions may be required to overify definitional equality between two
    types, and that, in turn, may lead to embedded uses of o-definitions
    getting unfolded and normalized.  

    Type checking a variable amounts to checking that it is in scope, which
    means it is looked up by name in the current context to see if the result
    is a variable of the same type: u, t, or o.  (The parser can infer from the
    grammar whether a variable is a t-variable, o-variable, or u-variable, but
    the parser ignores the environment.

    This version of the type checker will not handle undecidable aspects of
    definitional equality and will not produce a derivation tree.  Probably it
    can be enhanced to do so, perhaps by returning a closure that can be stored
    in an expression, which, when called later, will produce the derivation
    tree.

    Still to do: add type equality checking to the cases that require it.

    Failure to type is signaled with an exception. *)

exception TypeCheckingFailure of Typesystem.position * string
exception TypeCheckingFailure2 of Typesystem.position * string * Typesystem.position * string
exception TypeCheckingFailure3 of Typesystem.position * string * Typesystem.position * string * Typesystem.position * string
val ucheck : Typesystem.environment_type -> Typesystem.uExpr -> unit
val tcheck : Typesystem.environment_type -> Typesystem.tExpr -> unit
val ocheck : Typesystem.environment_type -> Typesystem.oExpr -> unit
val ucheck_okay : Typesystem.environment_type -> Typesystem.uExpr -> bool
val tcheck_okay : Typesystem.environment_type -> Typesystem.tExpr -> bool
val ocheck_okay : Typesystem.environment_type -> Typesystem.oExpr -> bool