(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

open Variables
open Typesystem

type alpha_eq = (var * var) list

val addalpha : var -> var -> alpha_eq -> alpha_eq

val testalpha : var -> var -> (var * var) list -> bool

module type S =
  sig
    val uequiv     : uContext -> lf_expr -> lf_expr -> bool
    val term_equiv : uContext -> lf_expr -> lf_expr -> bool
    val type_equiv : uContext -> lf_type -> lf_type -> bool
  end

module UEqual : S
module UEquivA : S
