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
type tHead = | T_El | T_El' | T_U | T_U' | T_Pi | T_Pi' | T_Sigma | T_Pt
             | T_Coprod | T_Coprod2 | T_Empty | T_IP | T_Id | T_Proof

(** Labels for o-expressions of TS. *)
type oHead =
  | O_u | O_j | O_ev | O_ev' | O_lambda | O_lambda' | O_forall | O_pair | O_pr1 | O_pr2 | O_total
  | O_pt | O_pt_r | O_tt | O_coprod | O_ii1 | O_ii2 | O_sum | O_empty | O_empty_r
  | O_c | O_ip_r | O_ip | O_paths | O_refl | O_J | O_rr0 | O_rr1
  | O_nat | O_nat_r | O_O | O_S

(** Labels for w-expressions of TS.  They are witnesses to "extended" judgments. *)
type wHead =
  | W_Wrefl | W_Wsymm | W_Wtrans | W_wrefl | W_wsymm | W_wtrans | W_wconv
  | W_wconveq | W_weleq | W_wpi1 | W_wpi2 | W_wlam | W_wl1 | W_wl2 | W_wev
  | W_wevt1 | W_wevt2 | W_wevf | W_wevo | W_wbeta | W_weta

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
  | F_wexp
      (* the next four are types, whose objects are witnesses; we use these as containers for the judgments of TTS *)
  | F_istype_witness
  | F_hastype_witness			(* i.e., p:o:T means p is of type o:T and is a witness that o is of type T *)
  | F_type_equality_witness
  | F_object_equality_witness
      (* the next four are judgments, with no objects when running in TTS mode, or with LF derivation trees as objects when running in LF mode *)
  | F_witnessed_istype
  | F_witnessed_hastype			(* i.e., p:o:T is a judgment, which must be derived *)
  | F_witnessed_type_equality
  | F_witnessed_object_equality
      (* the next one is needed just to accommodate undefined type constants encountered by the parser *)
  | F_undeclared_type_constant of position * string

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
  | W of wHead			(** labels for w-expressions of TS *)
  | V of var			(** labels for variables of TS *)
  | TAC of tactic_expr		(** An empty hole, to be filled in later by calling a tactic routine. *)

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
  | Tactic_index of int				 (* $3 *)
  | Tactic_name of string			 (* $foo *)
  | Tactic_sequence of tactic_expr * tactic_expr (* $(a;b;c) *)

let name_F_Pi = "Pi"

let ( @@ ) f x : lf_type = nowhere 3 (F_Apply(f,x))

let uexp = F_uexp @@ []
let wexp = F_wexp @@ []
let texp = F_texp @@ []
let oexp = F_oexp @@ []

let arrow a b = nowhere 4 (F_Pi(Var "_", a, b))
let ( @-> ) = arrow

let istype t = F_istype @@ [t]				       (* t Type *)
let hastype o t = F_hastype @@ [o;t]			       (* o : t *)
let ulevel_equality u u' = F_ulevel_equality @@ [u;u']	       (* u ~ u' *)
let type_uequality t t' = F_type_uequality @@ [t;t']	       (* t ~ t' *)
let type_equality t t' = F_type_equality @@ [t;t']	       (* t = t' *)
let object_uequality o o' t = F_object_uequality @@ [o;o';t]   (* o ~ o' : t *)
let object_equality o o' t = F_object_equality @@ [o;o';t]     (* o = o' : t *)

let istype_witness t = F_istype_witness @@ [t]		       (* t Type *)
let hastype_witness o t = F_hastype_witness @@ [o;t]	       (* o : t *)
let type_equality_witness t t' = F_type_equality_witness @@ [t;t'] (* t = t' *)
let object_equality_witness o o' t = F_object_equality_witness @@ [ o;o';t] (* o = o' : t *)

let witnessed_istype p t = F_witnessed_istype @@ [p;t]	       (* p : t Type *)
let witnessed_hastype p o t = F_witnessed_hastype @@ [p;o;t]   (* p : o : t *)
let witnessed_type_equality p t t' = F_witnessed_type_equality @@ [p;t;t'] (* p : t = t' *)
let witnessed_object_equality p o o' t = F_witnessed_object_equality @@ [ p;o;o';t] (* p : o = o' : t *)

let a_type = F_a_type @@ []				       (* |- T Type *)
let obj_of_type t = F_obj_of_type @@ [t]		       (* |- x : T *)
let judged_type_equal t u = F_judged_type_equal @@ [t;u]       (* |- T = U *)
let judged_obj_equal t x y = F_judged_obj_equal @@ [t;x;y]     (* |- x = y : T *)

let texp1 = oexp @-> texp
let texp2 = oexp @-> oexp @-> texp
let texp3 = oexp @-> oexp @-> oexp @-> texp

let oexp1 = oexp @-> oexp
let oexp2 = oexp @-> oexp @-> oexp
let oexp3 = oexp @-> oexp @-> oexp @-> oexp

let wexp_w = oexp @-> wexp @-> wexp
let texp_w = oexp @-> wexp @-> texp
let oexp_w = oexp @-> wexp @-> oexp

let uhead_to_lf_type = function	(* optimize later by precomputing the constant return values *)
  | U_next -> uexp @-> uexp
  | U_max -> uexp @-> uexp @-> uexp

let thead_to_lf_type = function	(* optimize later by precomputing the constant return values *)
  | T_El -> oexp @-> texp
  | T_El' -> oexp @-> wexp @-> texp
  | T_U -> uexp @-> texp
  | T_U' -> texp
  | T_Pi -> texp @-> texp1 @-> texp
  | T_Pi' -> texp @-> texp_w @-> texp
  | T_Sigma -> texp @-> texp1 @-> texp
  | T_Pt -> texp
  | T_Coprod -> texp @-> texp @-> texp
  | T_Coprod2 -> texp @-> texp @-> texp1 @-> texp1 @-> texp
  | T_Empty -> texp
  | T_IP -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> texp
  | T_Id -> texp @-> oexp @-> oexp @-> texp
  | T_Proof -> wexp @-> oexp @-> texp @-> texp

let ohead_to_lf_type = function	(* optimize later by precomputing the constant return values *)
  | O_u -> uexp @-> oexp
  | O_j -> uexp @-> uexp @-> oexp
  | O_ev -> oexp @-> oexp @-> texp @-> texp1 @-> oexp
  | O_ev' -> oexp @-> oexp @-> texp @-> texp_w @-> oexp
  | O_lambda -> texp @-> oexp1 @-> oexp
  | O_lambda' -> texp @-> oexp_w @-> oexp
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
  | O_nat -> oexp
  | O_O -> oexp
  | O_S -> oexp
  | O_nat_r -> oexp @-> oexp @-> oexp @-> texp1 @-> oexp

let whead_to_lf_type = function	(* optimize later by precomputing the constant return values *)
  | W_Wrefl -> wexp
  | W_Wsymm -> wexp @-> wexp
  | W_Wtrans -> wexp @-> wexp @-> texp @-> wexp
  | W_wrefl -> wexp @-> wexp @-> wexp
  | W_wsymm -> wexp @-> wexp
  | W_wtrans -> wexp @-> wexp @-> oexp @-> wexp
  | W_wconv -> wexp @-> wexp @-> wexp
  | W_wconveq -> wexp @-> wexp @-> texp @-> wexp
  | W_weleq -> wexp @-> wexp
  | W_wpi1 -> wexp @-> wexp
  | W_wpi2 -> wexp_w @-> wexp
  | W_wlam -> wexp_w @-> wexp
  | W_wl1 -> wexp @-> wexp @-> wexp
  | W_wl2 -> wexp @-> wexp
  | W_wev -> wexp @-> wexp @-> wexp
  | W_wevt1 -> wexp @-> wexp @-> wexp @-> wexp
  | W_wevt2 -> wexp @-> wexp @-> wexp @-> wexp
  | W_wevf -> wexp @-> wexp @-> wexp
  | W_wevo -> wexp @-> wexp @-> wexp @-> wexp
  | W_wbeta -> wexp @-> wexp_w @-> wexp
  | W_weta -> wexp @-> wexp

type vartype =
  | SingleVariable of int
  | WitnessPair of int

type vardist = int list list
let head_to_vardist = function (* optimize later by precomputing the constant return values *)
  | W W_wpi2 -> Some (1, [ WitnessPair 0] :: [])
  | W W_wlam -> Some (1, [ WitnessPair 0] :: [])
  | W W_wbeta -> Some (1, [] :: [ WitnessPair 0 ] :: [])
  | T T_Coprod2 -> Some (2, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 1] :: [])
  | O O_ip_r -> Some (5, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [] :: [ SingleVariable 3; SingleVariable 4] :: [] :: [])
  | T T_IP -> Some (3, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [])
  | O O_ev -> Some (1, [] :: [] :: [] :: [ SingleVariable 0] :: [])
  | O O_ev' -> Some (1, [] :: [] :: [] :: [ WitnessPair 0 ] :: [])
  | T T_Pi | T T_Sigma | O O_lambda -> Some (1, [] :: [ SingleVariable 0] :: [])
  | T T_Pi' | O O_lambda' -> Some (1, [] :: [ WitnessPair 0] :: [])
  | O O_forall -> Some (1, [] :: [] :: [] :: [ SingleVariable 0] :: [])
  | O O_pair -> Some (1, [] :: [] :: [ SingleVariable 0] :: [])
  | O O_pr1 | O O_pr2 -> Some (1, [] :: [ SingleVariable 0] :: [] :: [])
  | O O_total -> Some (1, [] :: [] :: [] :: [ SingleVariable 0] :: [])
  | O O_pt_r -> Some (1, [] :: [ SingleVariable 0] :: [])
  | O O_c -> Some (3, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [] :: [] :: [])
  | O O_ip -> Some (3, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [])
  | O O_J -> Some (2, [] :: [] :: [] :: [] :: [] :: [ SingleVariable 0; SingleVariable 1] :: [])
  | O O_nat_r -> Some(1, [] :: [] :: [] :: [SingleVariable 0] :: [])
  | _ -> None

(** The "kinds" of LF.

    Objects are classified by their type, and (parametrized) types are classified by their kind.

    Notation: constructors starting with "K_" refer to kinds of LF. *)
type lf_kind =
  | K_ulevel
  | K_expression
  | K_primitive_judgment
  | K_judgment
  | K_judged_expression
  | K_witnessed_judgment
  | K_Pi of var * lf_type * lf_kind

let ( @@-> ) a b = K_Pi(Var "_", a, b)

let istype_kind = texp @@-> K_primitive_judgment

let hastype_kind = oexp @@-> texp @@-> K_judgment

let type_equality_kind = texp @@-> texp @@-> K_judgment

let object_equality_kind = oexp @@-> oexp @@-> texp @@-> K_judgment

let ulevel_equality_kind = uexp @@-> uexp @@-> K_judgment

let type_uequality_kind = texp @@-> texp @@-> K_primitive_judgment

let object_uequality_kind = oexp @@-> oexp @@-> texp @@-> K_primitive_judgment

let a_type_kind = K_judged_expression

let obj_of_type_kind = a_type @@-> K_judged_expression

let judged_kind_equal_kind = a_type @@-> a_type @@-> K_judged_expression

let istype_witness_kind = texp @@-> K_witnessed_judgment (* unused by VV *)
let hastype_witness_kind = oexp @@-> texp @@-> K_witnessed_judgment
let type_equality_witness_kind = texp @@-> texp @@-> K_witnessed_judgment
let object_equality_witness_kind = oexp @@-> oexp @@-> texp @@-> K_witnessed_judgment

let witnessed_istype_kind = wexp @@-> texp @@-> K_witnessed_judgment (* unused by VV *)
let witnessed_hastype_kind = wexp @@-> oexp @@-> texp @@-> K_witnessed_judgment
let witnessed_type_equality_kind = wexp @@-> texp @@-> texp @@-> K_witnessed_judgment
let witnessed_object_equality_kind = wexp @@-> oexp @@-> oexp @@-> texp @@-> K_witnessed_judgment

let var_to_lf v = nowhere 1 (APPLY(V v,END))

let judged_obj_equal_kind =
  K_Pi(Var "T",
       a_type,
       obj_of_type (var_to_lf (VarRel 0))
       @@-> obj_of_type (var_to_lf (VarRel 1))
	 @@-> K_judged_expression)

let tfhead_to_kind = function
  | F_uexp -> K_ulevel
  | F_wexp | F_texp | F_oexp -> K_expression
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

  | F_istype_witness -> istype_witness_kind
  | F_hastype_witness -> hastype_witness_kind
  | F_type_equality_witness -> type_equality_witness_kind
  | F_object_equality_witness -> object_equality_witness_kind

  | F_witnessed_istype -> witnessed_istype_kind
  | F_witnessed_hastype -> witnessed_hastype_kind
  | F_witnessed_type_equality -> witnessed_type_equality_kind
  | F_witnessed_object_equality -> witnessed_object_equality_kind

  | F_undeclared_type_constant(pos,name) -> raise (UndeclaredTypeConstant(pos,name))

(** Subordination: see section 2.4 of Mechanizing Meta-theory by Harper and Licata *)
type kind_comparison = K_equal | K_less | K_greater | K_incomparable

let rec ultimate_kind = function
  | K_ulevel
  | K_expression
  | K_judgment
  | K_witnessed_judgment
  | K_primitive_judgment
  | K_judged_expression as k -> k
  | K_Pi (v,t,k) -> ultimate_kind k

let rec compare_kinds k l =
  let k = ultimate_kind k in
  let l = ultimate_kind l in
  if k = l then K_equal else
  match k,l with
  | K_primitive_judgment, K_judgment
  | K_judgment,           K_primitive_judgment
      -> K_equal
  | K_ulevel,             _
  | K_expression,         K_judgment
  | K_expression,         K_primitive_judgment
  | K_expression,         K_witnessed_judgment
  | K_primitive_judgment, K_witnessed_judgment
    -> K_less
  | _,                    K_ulevel
  | K_judgment,           K_expression
  | K_primitive_judgment, K_expression
  | K_witnessed_judgment, K_expression
  | K_witnessed_judgment, K_primitive_judgment
    -> K_greater
  | _ -> K_incomparable

(** Contexts. *)

module MapString = Map.Make(String)

type environment = {
    state : int;
    tts_context : (var * var * lf_expr) list; (* access by relative index *)
    global_tts_context : lf_type MapString.t;
    lf_context : (var * lf_type) list;
    global_lf_context : lf_type MapString.t;
  }

let empty_context = {
  state = 0;
  tts_context = [];
  global_tts_context = MapString.empty;
  lf_context = [];
  global_lf_context = MapString.empty
}

let interactive = ref false

let incr_state env =
  if !interactive
  then { env with state = env.state + 1 }
  else env

let lf_bind env v t = { env with lf_context = (v,t) :: env.lf_context }

let global_lf_bind env v t = { env with global_lf_context = MapString.add (vartostring v) t env.global_lf_context }

let tts_bind env p v t = { env with tts_context = (p,v,t) :: env.tts_context }

let global_tts_bind env v t = { env with global_tts_context = MapString.add (vartostring v) t env.global_tts_context }

let ts_bind env v t =
  let v' = witness_var v in
  { env with tts_context = (v',v,t) :: env.tts_context }

let tts_fetch env v =
  let rec repeat = function
      [] -> raise Not_found
    | (p,o,t)::l ->
        if compare o v = 0 then (p,t) else
        if compare p v = 0 then raise Internal else (*debugging only*)
        repeat l
  in
  repeat env.tts_context

let ts_fetch env v =
  let (p,t) = tts_fetch env v in
  t

let tts_fetch_w env w =
  let rec repeat = function
      [] -> raise Not_found
    | (p,o,t)::l ->
        if compare p w = 0 then (o,t) else
        if compare o w = 0 then raise Internal else (*debugging only*)
        repeat l
  in
  repeat env.tts_context

type uContext = UContext of var marked list * (lf_expr * lf_expr) marked list

let empty_uContext = UContext([],[])

(** Tactics. *)

type surrounding_component =
  | S_argument of int
  | S_projection of int
  | S_body

type surrounding = (surrounding_component * lf_expr option * lf_type option) list

type tactic_return =
  | TacticFailure
  | TacticSuccess of lf_expr

type tactic_function =
       surrounding         (* the ambient APPLY(...), if any, and the index among its head and arguments of the hole *)
    -> environment						      (* the active context *)
    -> position							      (* the source code position of the tactic hole *)
    -> lf_type							      (* the type of the hole, e.g., [texp] *)
    -> spine							      (* the arguments *)
 -> tactic_return						      (* the proffered expression *)

let tactics : (string * tactic_function) list ref = ref []

let add_tactic (name,f) = tactics := (name,f) :: !tactics

(*
  Local Variables:
  compile-command: "make -C .. src/typesystem.cmo "
  End:
 *)
