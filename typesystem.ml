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

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
 *)

(** Labels for u-expressions of TS. *)
type uHead = | U_next | U_max

let uheads = [ U_max; U_next ]

let uhead_to_string = function | U_next -> "next" | U_max -> "max"

(** The various labels for t-expressions of TS. *)

type tHead = | T_El | T_U | T_Pi | T_Sigma | T_Pt 
             | T_Coprod | T_Coprod2 | T_Empty | T_IP | T_Id

let theads = [ T_El; T_U; T_Pi; T_Sigma; T_Pt; T_Coprod; T_Coprod2; T_Empty; T_IP; T_Id ]

let thead_to_string = function
  | T_El -> "El"  | T_U -> "U"  | T_Pi -> "Pi"  | T_Sigma -> "Sigma"
  | T_Pt -> "Pt"  | T_Coprod -> "Coprod"  | T_Coprod2 -> "Coprod2"
  | T_Empty -> "Empty"  | T_IP -> "IP"  | T_Id -> "Id"

(** The various labels for o-expressions of TS. *)
type oHead =
  | O_u  | O_j  | O_ev  | O_lambda  | O_forall  | O_pair  | O_pr1  | O_pr2  | O_total
  | O_pt  | O_pt_r  | O_tt  | O_coprod  | O_ii1  | O_ii2  | O_sum  | O_empty  | O_empty_r
  | O_c  | O_ip_r  | O_ip  | O_paths  | O_refl  | O_J  | O_rr0  | O_rr1

let ohead_to_string = function
  | O_u -> "u"  | O_j -> "j"  | O_ev -> "ev"  | O_lambda -> "lambda"
  | O_forall -> "forall"  | O_pair -> "pair"  | O_pr1 -> "pr1"
  | O_pr2 -> "pr2"  | O_total -> "total"  | O_pt -> "pt"  | O_pt_r -> "pt_r"
  | O_tt -> "tt"  | O_coprod -> "coprod"  | O_ii1 -> "ii1"  | O_ii2 -> "ii2"
  | O_sum -> "sum"  | O_empty -> "empty"  | O_empty_r -> "empty_r"  | O_c -> "c"
  | O_ip_r -> "ip_r"  | O_ip -> "ip"  | O_paths -> "paths"  | O_refl -> "refl"
  | O_J -> "J"  | O_rr0 -> "rr0"  | O_rr1 -> "rr1"

let oheads = [ O_u; O_j; O_ev; O_lambda; O_forall; O_pair; O_pr1; O_pr2;
  O_total; O_pt; O_pt_r; O_tt; O_coprod; O_ii1; O_ii2; O_sum; O_empty;
  O_empty_r; O_c; O_ip_r; O_ip; O_paths; O_refl; O_J; O_rr0; O_rr1 ]

(** Variables *)

type var =				(* a variable *)
  | Var of string
  | VarGen of int * string
  | VarUnused
  | VarDefined of string * int         (** A definition. *)

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ (string_of_int i)
  | VarUnused -> "_"
  | VarDefined (name,aspect) -> "[" ^ name ^ "." ^ (string_of_int aspect) ^ "]"

(** Tactics *)

type tactic_expr = 
  | Q_name of string
  | Q_index of int

    (** The type [label] accommodates the variables of LF, and the constants of
        LF, which in turn include the labels of TS, the inference rules of TS,
        and the definitions of TS (in various aspects).

	In parsing and printing, the constants have have names enclosed in
	brackets, e.g., [\[ev\]], reminiscent of the syntax for the labels on
	nodes of TS expressions.

	We implement "spine form", where applications are represented as [(f x
	y z ...)], with [f] not being an application, thus being a constant or
	a variable, i.e., being a "label".

	For definitions, we envision multiple aspects.  For example, aspect 1
	could be a t-expression T and aspect 2 could be a derivation of the
	judgment that T is a type.  Or aspect 1 could be an o-expression t,
	aspect 2 could be a type T, and aspect 3 could be a derivation of the
	judgment that t has type T.  Similarly for the other two types of
	judgment in TS. *)

type label =
  | U of uHead			(** labels for u-expressions of TS *)
  | T of tHead			(** labels for t-expressions of TS *)
  | O of oHead			(** labels for o-expressions of TS *)
  | V of var			(** labels for variables of TS *)

let labels = List.concat [
  List.map (fun h -> U h) uheads;
  List.map (fun h -> T h) theads;
  List.map (fun h -> O h) oheads
]

let label_to_string = function
  | V v -> vartostring v
  | U h -> "[" ^ uhead_to_string h ^ "]"
  | T h -> "[" ^ thead_to_string h ^ "]"
  | O h -> "[" ^ ohead_to_string h ^ "]"

let string_to_label = 
  let a = List.map (fun h -> label_to_string h, h) labels in
  let b = [
    ("[∏]", T T_Pi);
    ("[Σ]", T T_Sigma);
    ("[∐]", T T_Coprod);
    ("[λ]", O O_lambda);
    ("[∀]", O O_forall)] in
  List.concat [a;b]
	
(** Canonical terms include the atomic terms, as well as one new type of term
    (lambda expressions), which admits no top level simplification
    (evaluation). *)
type canonical_term = 
  | LAMBDA of var * canonical_term
	(** Lambda expression of LF. *)
  | Phi of atomic_term
	(** [Phi] is embeds TS expressions into LF expressions *)

(** An atomic term is one that isn't a lambda expression.

    In an atomic term, top level simplification (evaluation) may be possible;
    for example, a variable appearing as a label, with a defined value, could
    be replaced by its value, which is then applied to the arguments, if any. *)
and atomic_term = atomic_term' marked
and atomic_term' =
  | EmptyHole of int
    (** An empty hole, to be filled in later. *)
  | TacticHole of tactic_expr
    (** An empty hole, to be filled in later by calling a tactic routine writtn in OCAML. *)
  | APPLY of label * canonical_term list
    (** A variable or constant applied iteratively to its arguments, if any. *)

(** Expressions of LF are the canonical terms. *)
type lf_expr = canonical_term

(** Expressions of TS are the atomic terms.  The constructor Phi above
    implements the embedding from TS into LF. *)
type ts_expr = atomic_term

let rec get_pos_can (x:canonical_term) =
  match x with
  | Phi x -> get_pos x
  | LAMBDA(x,b) -> get_pos_can b

(** Notation. *)

let var_to_ts v = APPLY(V v,[])

let var_to_lf v = Phi (nowhere 1 (var_to_ts v))

(** Canonical type families of LF.

    The following type family constants for LF type families segregate TS
    expressions into three forms: u-expressions, t-expressions, and
    o-expressions, and they introduce the four forms of judgments.

    Notation: constructors starting with "F_" refer to type families of
    LF. *)
type tfHead =
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

type lf_type = bare_lf_type marked
and bare_lf_type =
  | F_Pi of var * lf_type * lf_type
  | F_APPLY of tfHead * lf_expr list
  | F_Singleton of (lf_expr * lf_type)

let tfhead_to_string = function
  | F_uexp -> "uexp"
  | F_texp -> "texp"
  | F_oexp -> "oexp"
  | F_istype -> "istype"
  | F_hastype -> "hastype"
  | F_ulevel_equality -> "uequal"
  | F_type_equality -> "tequal"
  | F_object_equality -> "oequal"
  | F_type_uequality -> "t-uequal"
  | F_object_uequality -> "o-uequal"

let tfheads = [ 
  F_uexp; F_texp; F_oexp; F_istype; F_hastype; F_ulevel_equality ;
  F_type_uequality; F_type_equality; F_object_uequality; F_object_equality ]

let tfhead_strings = List.map (fun x -> tfhead_to_string x, x) tfheads

let ( ** ) f x = nowhere 3 (F_APPLY(f,x))

let uexp = F_uexp ** []
let texp = F_texp ** []
let oexp = F_oexp ** []

let ( @-> ) a b = nowhere 4 (F_Pi(VarUnused, a, b))

let istype t = F_istype ** [t]
let hastype o t = F_hastype ** [o;t]
let ulevel_equality u u' = F_ulevel_equality ** [u;u']
let type_uequality t t' = F_type_uequality ** [t;t']
let type_equality t t' = F_type_equality ** [t;t']
let object_similariy o o' t = F_object_uequality ** [o;o';t]
let object_equality o o' t = F_object_equality ** [o;o';t]

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
  | O_paths -> texp @-> oexp @-> oexp @-> oexp
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
  | K_type
  | K_Pi of var * lf_type * lf_kind

let ( @@-> ) a b = K_Pi(VarUnused, a, b)

let tfhead_to_kind = function
  | F_uexp -> K_type
  | F_texp -> K_type
  | F_oexp -> K_type
  | F_istype -> texp @@-> K_type
  | F_hastype -> oexp @@-> texp @@-> K_type
  | F_ulevel_equality -> uexp @@-> uexp @@-> K_type
  | F_type_equality -> texp @@-> texp @@-> K_type
  | F_object_equality -> oexp @@-> oexp @@-> texp @@-> K_type
  | F_type_uequality -> texp @@-> texp @@-> K_type
  | F_object_uequality -> oexp @@-> oexp @@-> K_type

type oSubs = (var * ts_expr) list

(** Contexts. *)

type context = (var * lf_type) list

let lookup_type env v = List.assoc v env

let global_context : context ref = ref []

type uContext = UContext of var list * (ts_expr * ts_expr) list

let empty_uContext = UContext([],[])

let def_bind v (pos:position) o t (env:context) = (v, (pos,F_Singleton(o,t))) :: env

(* raise an exception when a certain fresh variable is generated *)
let genctr_trap = 0

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr;
    if !genctr = genctr_trap then raise DebugMe;
    if !genctr < 0 then raise GensymCounterOverflow;
    VarGen (!genctr, x)) in
  fun v -> match v with 
  | Var x | VarGen(_,x) -> newgen x
  | VarDefined _ | VarUnused -> raise Internal

let ts_bind (v,t) env = match v with
  | VarUnused -> env
  | v -> 
      (newfresh (Var "h") , hastype (var_to_lf v) (Phi t)) :: 
      (v,oexp) :: 
      env

let new_hole = 
  let counter = ref 0 in
  function () -> (
    let h = EmptyHole !counter in
    incr counter;
    h)

exception Internal_expr of lf_expr
exception Unimplemented_expr of lf_expr
exception TypeCheckingFailure of context * position * string
exception TypeCheckingFailure2 of context * position * string * position * string
exception TypeCheckingFailure3 of context * position * string * position * string * position * string

let fetch_type env pos v = 
  try List.assoc v env
  with Not_found -> 
    raise (TypeCheckingFailure (env, pos, ("unbound variable: "^(vartostring v))))

let label_to_type env pos = function
  | U h -> uhead_to_lf_type h
  | T h -> thead_to_lf_type h
  | O h -> ohead_to_lf_type h
  | V v -> fetch_type env pos v

let tactic_to_string : tactic_expr -> string = function
  | Q_name n -> "$" ^ n
  | Q_index n -> "$" ^ (string_of_int n)

(* 
  Local Variables:
  compile-command: "ocamlbuild typesystem.cmo "
  End:
 *)
