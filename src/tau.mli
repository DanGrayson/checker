 (** Computing the type of an o-expression.

     The function [tau] from the paper.  It produces the type of an o-expression [o] in a context [G],
     even if the expression is not yet known to be well-formed.
   *)


val tau : Typesystem.environment -> Typesystem.lf_expr -> Typesystem.lf_expr
