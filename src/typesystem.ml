(* -*- coding: utf-8 -*- *)

(** Voevodsky's type system TS mixed with the type system LF of Logical Frameworks (Edinburgh style).

@author Dan Grayson

    *)

(**

This file encodes the type system TS developed in the paper {i A universe
polymorphic type system}, by Vladimir Voevodsky, the version dated October,
2012.  We call that [UPTS].

There is also a preprint {i Description of LF in TS style}, by Vladimir
Voevodsky, dated November 27, 2012.  We call that [LFinTS].

  *)

open Error
open Variables

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
 *)

(** Labels for u-expressions of TS. *)
type uHead = | U_next | U_max

(** Labels for t-expressions of TS. *)
type tHead = | T_El | T_U | T_Pi | T_Sigma | T_Pt 
             | T_Coprod | T_Coprod2 | T_Empty | T_IP | T_Id

(** Labels for o-expressions of TS. *)
type oHead =
  | O_u  | O_j  | O_ev  | O_lambda  | O_forall  | O_pair  | O_pr1  | O_pr2  | O_total
  | O_pt  | O_pt_r  | O_tt  | O_coprod  | O_ii1  | O_ii2  | O_sum  | O_empty  | O_empty_r
  | O_c  | O_ip_r  | O_ip  | O_paths  | O_refl  | O_J  | O_rr0  | O_rr1

(** Canonical type families of LF.

    The following type family constants for LF type families segregate TS
    expressions into three forms: u-expressions, t-expressions, and
    o-expressions, and they introduce the four forms of judgments.

    Notation: constructors starting with "F_" refer to type families of
    LF. *)
type lf_type_head =
  | F_uexp
  | F_texp
  | F_oexp
  | F_istype
  | F_hastype
  | F_type_equality
  | F_object_equality
  | F_ulevel_equality
  | F_type_uequality			(* written with ~ in the paper *)
  | F_object_uequality			(* written with ~ in the paper *)
  | F_a_type
  | F_obj_of_type
  | F_judged_type_equal
  | F_judged_obj_equal

    (** The type [lf_expr_head] accommodates the variables of LF, and the constants of
        LF, which in turn include the labels of TS, the inference rules of TS,
        and the definitions of TS (in various aspects).

	In parsing and printing, the constants have have names enclosed in
	brackets, e.g., [\[ev\]], reminiscent of the syntax for the labels on
	nodes of TS expressions.

	We implement "spine form", where applications are represented as [(f x
	y z ...)], with [f] not being an application, thus being a constant or
	a variable, i.e., being a "lf_expr_head".

	For definitions, we envision multiple aspects.  For example, aspect 1
	could be a t-expression T and aspect 2 could be a derivation of the
	judgment that T is a type.  Or aspect 1 could be an o-expression t,
	aspect 2 could be a type T, and aspect 3 could be a derivation of the
	judgment that t has type T.  Similarly for the other two types of
	judgment in TS. *)
type lf_expr_head =
  | U of uHead			(** labels for u-expressions of TS *)
  | T of tHead			(** labels for t-expressions of TS *)
  | O of oHead			(** labels for o-expressions of TS *)
  | V of var			(** labels for variables of TS *)
  | TAC of tactic_expr		(** An empty hole, to be filled in later by calling a tactic routine. *)
  | FUN of lf_expr * lf_type
	(** In context with the spine, this is a [beta-redex] ready to be
	    reduced, i.e., it's a function [f] of type [t] and an argument
	    spine [args], and we're ready to apply [f] to [args].  The main
	    justification for introducing it is for implementing local
	    definitions with a head of the form [(x |-> b, (x:Singleton(a)) ->
	    B)]. *)

(** The expressions of LF, including the expressions of TS as instances of [APPLY].*)
and lf_expr = unmarked_expr marked
and unmarked_expr =
  | LAMBDA of var * lf_expr
	(** Lambda expression of LF. *)
  | CONS of lf_expr * lf_expr
	(** A pair of dependent type. *)
  | APPLY of lf_expr_head * spine
	(** A variable or constant or tactic applied iteratively to its
	    arguments, if any.  This includes the expressions of TS, with
	    something such as [\[ev\]] as the head and the branches as the
	    parts of the spine.

	    Because the head is a variable, we are blocked from further
	    evaluation, unless the variable has a definition (i.e., belongs to
	    a singleton type), in which case, the unfolding will happen when
	    the LF type checker needs to put the expression in weak head
	    reduced form. *)

(** A spine is basically a list of arguments to which the head function of an
    atomic term will be applied, in sequence, but with two new instructions,
    [CAR] and [CDR], which turn the tables on the function, expecting it to be
    a pair, and replacing it by the first or second component, respectively. *)
and spine =
  | ARG of lf_expr * spine
  | CAR of spine
  | CDR of spine
  | END

and lf_type = bare_lf_type marked
and bare_lf_type =
  | F_Pi of var * lf_type * lf_type
  | F_Sigma of var * lf_type * lf_type
  | F_Apply of lf_type_head * lf_expr list
  | F_Singleton of (lf_expr * lf_type)

(** Tactics *)
and tactic_expr = 
  | Tactic_hole of int			(* represented by _ *)
  | Tactic_name of string		(* represented by $foo *)
  | Tactic_index of int			(* represented by $n *)

let ( @@ ) f x : lf_type = nowhere 3 (F_Apply(f,x))

let uexp = F_uexp @@ []
let texp = F_texp @@ []
let oexp = F_oexp @@ []

let arrow a b = nowhere 4 (F_Pi(newunused(), a, b))
let ( @-> ) = arrow

let istype t = F_istype @@ [t]				       (* t Type *)
let hastype o t = F_hastype @@ [o;t]			       (* o : t *)
let ulevel_equality u u' = F_ulevel_equality @@ [u;u']	       (* u ~ u' *)
let type_uequality t t' = F_type_uequality @@ [t;t']	       (* t ~ t' *)
let type_equality t t' = F_type_equality @@ [t;t']	       (* t = t' *)
let object_uequality o o' t = F_object_uequality @@ [o;o';t]   (* o ~ o' : t *)
let object_equality o o' t = F_object_equality @@ [o;o';t]     (* o = o' : t *)
let a_type = F_a_type @@ []				       (* |- T Type *)
let obj_of_type t = F_obj_of_type @@ [t]			       (* |- x : T *)
let judged_type_equal t u = F_judged_type_equal @@ [t;u]       (* |- T = U *)
let judged_obj_equal t x y = F_judged_obj_equal @@ [t;x;y]     (* |- x = y : T *)

let texp1 = oexp @-> texp
let texp2 = oexp @-> oexp @-> texp
let texp3 = oexp @-> oexp @-> oexp @-> texp

let oexp1 = oexp @-> oexp
let oexp2 = oexp @-> oexp @-> oexp
let oexp3 = oexp @-> oexp @-> oexp @-> oexp

let uhead_to_lf_type = function
  | U_next -> uexp @-> uexp
  | U_max -> uexp @-> uexp @-> uexp

let thead_to_lf_type = function
  | T_El -> oexp @-> texp
  | T_U -> uexp @-> texp
  | T_Pi -> texp @-> texp1 @-> texp
  | T_Sigma -> texp @-> texp1 @-> texp
  | T_Pt -> texp
  | T_Coprod -> texp @-> texp @-> texp
  | T_Coprod2 -> texp @-> texp @-> texp1 @-> texp1 @-> texp
  | T_Empty -> texp
  | T_IP -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> texp
  | T_Id -> texp @-> oexp @-> oexp @-> texp

let ohead_to_lf_type = function
  | O_u -> uexp @-> oexp
  | O_j -> uexp @-> uexp @-> oexp
  | O_ev -> oexp @-> oexp @-> texp1 @-> oexp
  | O_lambda -> texp @-> oexp1 @-> oexp
  | O_forall -> uexp @-> uexp @-> oexp @-> oexp1 @-> oexp
  | O_pair -> oexp @-> oexp @-> texp1 @-> oexp
  | O_pr1 -> texp @-> texp1 @-> oexp @-> oexp
  | O_pr2 -> texp @-> texp1 @-> oexp @-> oexp
  | O_total -> uexp @-> uexp @-> oexp @-> oexp1 @-> oexp
  | O_pt -> oexp
  | O_pt_r -> oexp @-> texp1 @-> oexp
  | O_tt -> oexp
  | O_coprod -> uexp @-> uexp @-> oexp @-> oexp @-> oexp
  | O_ii1 -> texp @-> texp @-> oexp @-> oexp
  | O_ii2 -> texp @-> texp @-> oexp @-> oexp
  | O_sum -> texp @-> texp @-> oexp @-> oexp @-> oexp @-> texp1 @-> oexp
  | O_empty -> oexp
  | O_empty_r -> texp @-> oexp @-> oexp
  | O_c -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> oexp @-> oexp @-> oexp
  | O_ip_r -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> oexp @-> texp2 @-> oexp @-> oexp
  | O_ip -> oexp @-> oexp @-> oexp1 @-> oexp2 @-> oexp3 @-> oexp
  | O_paths -> uexp @-> oexp @-> oexp @-> oexp @-> oexp
  | O_refl -> texp @-> oexp @-> oexp
  | O_J -> texp @-> oexp @-> oexp @-> oexp @-> oexp @-> texp2 @-> oexp
  | O_rr0 -> uexp @-> uexp @-> oexp @-> oexp @-> oexp @-> oexp
  | O_rr1 -> uexp @-> oexp @-> oexp @-> oexp

type vardist = int list list
let head_to_vardist = function
  | T T_Coprod2 -> Some (2, [] :: [] :: [0] :: [1] :: [])
  | O O_ip_r -> Some (5, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [] :: [3;4] :: [] :: [])
  | T T_IP -> Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [])
  | O O_ev -> Some (1, [] :: [] :: [0] :: [])
  | T T_Pi | T T_Sigma | O O_lambda -> Some (1, [] :: [0] :: [])
  | O O_forall -> Some (1, [] :: [] :: [] :: [0] :: [])
  | O O_pair -> Some (1, [] :: [] :: [0] :: [])
  | O O_pr1 | O O_pr2 -> Some (1, [] :: [0] :: [] :: [])
  | O O_total -> Some (1, [] :: [] :: [] :: [0] :: [])
  | O O_pt_r -> Some (1, [] :: [0] :: [])
  | O O_c -> Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [] :: [] :: [])
  | O O_ip -> Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [])
  | O O_J -> Some (2, [] :: [] :: [] :: [] :: [] :: [0;1] :: [])
  | _ -> None

(** The "kinds" of LF. 

    Notation: constructors starting with "K_" refer to kinds of LF. *)
type lf_kind =
  | K_expression
  | K_judgment
  | K_judged_expression
  | K_judged_expression_judgment
  | K_Pi of var * lf_type * lf_kind

let ( @@-> ) a b = K_Pi(newunused(), a, b)

let some_type () = 
  let v = newfresh (Var "T") in
  nowhere 123 (F_Sigma(v,texp,istype (nowhere 124 (APPLY(V v,END)))))

let some_object_of_type t = 
  let v = newfresh (Var "x") in
  nowhere 125 (F_Sigma(v,oexp,hastype (nowhere 126 (APPLY(V v,END))) t))

let this_object_of_type pos o t = 
  let v = newfresh (Var "x") in
  with_pos pos (F_Sigma(v,with_pos pos (F_Singleton(o,oexp)),hastype (nowhere 126 (APPLY(V v,END))) t))

let k_pi t k =
  let v = newfresh (Var "T") in
  let v' = nowhere 126 (APPLY(V v,END)) in
  K_Pi(v,t,k v')

let istype_kind = texp @@-> K_judgment

let hastype_kind = oexp @@-> texp @@-> K_judgment

let type_equality_kind = texp @@-> texp @@-> K_judgment

let object_equality_kind = oexp @@-> oexp @@-> texp @@-> K_judgment

let ulevel_equality_kind = uexp @@-> uexp @@-> K_judgment

let type_uequality_kind = texp @@-> texp @@-> K_judgment

let object_uequality_kind = oexp @@-> oexp @@-> texp @@-> K_judgment

let a_type_kind = K_judged_expression

let obj_of_type_kind = a_type @@-> K_judged_expression

let judged_kind_equal_kind = a_type @@-> a_type @@-> K_judged_expression_judgment

let var_to_lf v = nowhere 1 (APPLY(V v,END))

let judged_obj_equal_kind = 
  let t = newfresh (Var "T") in
  let tt = var_to_lf t in
  K_Pi(t, a_type, obj_of_type tt @@-> obj_of_type tt @@-> K_judged_expression_judgment)

let tfhead_to_kind = function
  | F_uexp -> K_expression
  | F_texp -> K_expression
  | F_oexp -> K_expression
  | F_istype -> istype_kind
  | F_hastype -> hastype_kind
  | F_ulevel_equality -> ulevel_equality_kind
  | F_type_equality -> type_equality_kind
  | F_object_equality -> object_equality_kind
  | F_type_uequality -> type_uequality_kind
  | F_object_uequality -> object_uequality_kind
  | F_a_type -> a_type_kind
  | F_obj_of_type -> obj_of_type_kind
  | F_judged_type_equal -> judged_kind_equal_kind
  | F_judged_obj_equal -> judged_obj_equal_kind

type oSubs = (var * lf_expr) list

(** Contexts. *)

type context = (var * lf_type) list

type uContext = UContext of var marked list * (lf_expr * lf_expr) marked list

let empty_uContext = UContext([],[])

(** Tactics. *)

type surrounding = (int option * lf_expr * lf_type option) list

type tactic_return =
  | TacticFailure
  | TacticSuccess of lf_expr

type tactic_function =
       surrounding         (* the ambient APPLY(...), if any, and the index among its head and arguments of the hole *)        
    -> context							      (* the active context *)
    -> position							      (* the source code position of the tactic hole *)
    -> lf_type							      (* the type of the hole, e.g., [texp] *)
 -> tactic_return								 (* the proffered expression *)

let tactics : (string * tactic_function) list ref = ref []

(* 
  Local Variables:
  compile-command: "make -C .. src/typesystem.cmo "
  End:
 *)
