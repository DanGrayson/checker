(** In this file we do typechecking.  

    For a t-expression, this just amounts to being well-formed, since types
    have no type.  For an o-expression, it's a meta-theorem that the type turns
    out to equal the result that the function tau yields.  The body of a
    definition is checked in its local context, as a t-expression or as an
    o-expression; it's a meta-theorem that later substitution preserves types,
    so unfolding of o-definitions embedded in other expressions is not needed
    at the point they are encounted, as the type of the result obtained by
    unfolding is more easily obtained by substitution; unfolding of
    t-definitions may be required to verify definitional equality between two
    types, and that, in turn, may lead to embedded uses of o-definitions
    getting unfolded and normalized.  

    Type checking a variable amounts to checking that it is in scope, which
    means it is looked up by name in the current context to see if the result
    is a variable of the same type: u, t, or o.  (The parser can infer from the
    grammar whether a variable is a t-variable, o-variable, or u-variable, but
    the parser ignores the environment.

    This version of the type checker will not handle undecidable aspects of
    definitional equality and will not produce a derivation tree.

    Failure to type is signaled with an exception. *)

open Typesystem
exception TypeCheckingFailure of position * string

let rec ucheck (env:environment_type) (u:uExpr) = match strip_pos u with
  | Uvariable UVar s -> (
      match (
	try List.assoc s env.lookup_order
	with Not_found -> raise (TypeCheckingFailure (get_pos u, "encountered unbound u-variable: "^s)))
      with 
	U _ -> ()
      | T _ -> raise (TypeCheckingFailure (get_pos u, "expected a u-variable but found a t-variable: "^s))
      | O _ -> raise (TypeCheckingFailure (get_pos u, "expected a u-variable but found an o-variable: "^s)))
  | Uplus (u,n) -> ucheck env u
  | Umax (u,v) -> ucheck env u; ucheck env v
  | UEmptyHole
  | UNumberedEmptyHole _ -> raise (TypeCheckingFailure(get_pos u, "empty hole for u-expression found"))
  | U_def (d,u) -> raise NotImplemented

let rec tcheck (env:environment_type) (t:tExpr) = ()
and ocheck (env:environment_type) (o:oExpr) = ()

let ucheck_okay env x = try ucheck env x; true with TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with TypeCheckingFailure _ -> false
