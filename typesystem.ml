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
type uHead =
  | U_next
	(** With a [M], denoting [M+1], the successor of [M]. *)
  | U_max
	(** A pair [(M,M')] denoting [max(M,M')]. *)

let uheads = [ U_max; U_next ]

let uhead_to_string = function
  | U_next -> "next"
  | U_max -> "max"

(** The various labels for t-expressions of TS. *)
type tHead =
	(* TS0: *)
  | T_El
      (** [T_El]; converts an object term into the corresponding type term *)
  | T_U
      (** [T_U m]; a u-level expression, as a type *)
  | T_Pi
      (** [T_Pi(T,(x,T')) <--> \[Pi;x\](T,T')] *)
      (* TS1: *)
  | T_Sigma
      (** [T_Sigma(T,(x,T')) <--> \[Sigma;x\](T,T')] *)
      (* TS2: *)
  | T_Pt
      (** Corresponds to [Pt]() in the paper; the unit type *)
      (* TS3: *)
  | T_Coprod
  | T_Coprod2
      (* TS4: *)
  | T_Empty
      (** The empty type.  
	  
	  Voevodsky doesn't list this explicitly in the definition of TS4, but it gets used in derivation rules, so I added it.
	  Perhaps he intended to write [\[T_El\](\[empty\]())] for it. *)
      (* TS5: *)
  | T_IC
	(** [T_IC(A,a,(x,B),(x,(y,D)),(x,(y,(z,q)))) <--> \[IC;x,y,z\](A,a,B,D,q)] *)
      (* TS6: *)
  | T_Id
      (** Identity type; paths type. *)
      (* TS7: *)
      (* end of TS *)

let theads = [ T_El; T_U; T_Pi; T_Sigma; T_Pt; T_Coprod; T_Coprod2; T_Empty; T_IC; T_Id ]

let thead_to_string = function
  | T_El -> "El"
  | T_U -> "U"
  | T_Pi -> "Pi"
  | T_Sigma -> "Sigma"
  | T_Pt -> "Pt"
  | T_Coprod -> "Coprod"
  | T_Coprod2 -> "Coprod2"
  | T_Empty -> "Empty"
  | T_IC -> "IC"
  | T_Id -> "Id"

(** The various labels for o-expressions of TS. *)
type oHead =
    (* TS0: *)
  | O_u
	(** [u]; universe as an object. *)
  | O_j
	(** [j](U,U') *)
  | O_ev
	(** [O_ev(f,o,(x,T)) <--> \[ev;x\](f,o,T)]
	    
	    Application of the function [f] to the argument [o].
	    
	    Here [T], with the type of [o] replacing [x], gives the type of the result.

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_lambda
	(** [O_lambda(T,(x,o)) <--> \[lambda;x\](T,o)] *)
  | O_forall
	(** [O_forall(M,M',o,(x,o')) <--> \[forall;x\]([M],[M'],o,o')]
	    
	    [O_forall] is the object term corresponding to [Pi].
	    The type of the term is given by the max of the two u-levels. *)
      (* TS1: *)
  | O_pair
	(** [O_pair(a,b,(x,T)) <--> \[pair;x\](a,b,T)]
	    
	    An instance of [Sigma]. *)
  | O_pr1
	(** [O_pr1(T,(x,T'),o) <--> \[pr1;x\](T,T',o)] 

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_pr2
	(** [O_pr2(T,(x,T'),o) <--> \[pr2;x\](T,T',o)] 

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_total
	(** [O_total(m1,m2,o1,(x,o2)) <--> \[total;x\](m1,m2,o1,o2)]

	    Corresponds to [total] or [prod] in the paper. *)
	(* TS2: *)
  | O_pt
      (** Corresponds to [\[pt\]] in the paper. *)
  | O_pt_r
	(** [O_pt_r(o,(x,T)) <--> \[pt_r;x\](o,T)]
	    
	    [O_pt_r] is the eliminator for [Pt]. *)
  | O_tt
      (** [O_tt <--> \[tt\]()]
	  
	  [O_tt] is the unique instance of the unit type [Pt]. *)
      (* TS3: *)
  | O_coprod
	(** The type of the term is given by the [max] of the two u-levels. *)
  | O_ii1
	(** The type of a term [O_ii1(T,T',o)] is [Coprod(T,T')]; here [o] has type [T] *)
  | O_ii2
	(** The type of a term [O_ii2(T,T',o)] is [Coprod(T,T')]; here [o] has type [T'] *)
  | O_sum
	(** The type of a term [O_sum(T,T',s,s',o,(x,S))] is [S], with [x] replaced by [o]. *)
	(* TS4: *)
  | O_empty
      (** [ O_empty <--> \[empty\]() ]
				    
	  The type of [\[empty\]] is the smallest universe, [uuu0]. 

	  Remember to make [El]([empty]()) reduce to [Empty]().
       *)
  | O_empty_r
	(** The elimination rule for the empty type.

	    The type of [O_empty_r(T,o)] is [T].  Here the type of [o] is [Empty], the empty type. *)
  | O_c
	(** Corresponds to [c] in the paper. *)
  | O_ic_r
	(** [ic_r] is the elimination rule for inductive types (generalized W-types) *)
  | O_ic
	(** Corresponds to [ic].  Its type is the max of the three u-level expressions. *)
	(* TS6: *)
  | O_paths
	(** The object corresponding to the identity type [Id].  

	    Its type is the type corresponding to the given universe level. *)
  | O_refl
	(** Reflexivity, or the constant path. 
	    
	    The type of [O_refl(T,o)] is [Id(T,o,o)]. *)
  | O_J
	(** The elimination rule for Id; Id-elim. *)
      (* TS7: *)
  | O_rr0
	(** Resizing rule.

	    The type of [O_rr0(M_2,M_1,s,t,e)] is [U(M_1)], resized downward from [U M_2].

	    By definition, the subexpressions [t] and [e] are not essential.
	 *)
  | O_rr1
	(** Resizing rule.

	    The type of [O_rr1(M,a,p)] is [U uuu0], resized downward from [U M].

	    By definition, the subexpression [p] is not essential.
	 *)
      (* end of TS *)

let ohead_to_string = function
  | O_u -> "u"
  | O_j -> "j"
  | O_ev -> "ev"
  | O_lambda -> "lambda"
  | O_forall -> "forall"
  | O_pair -> "pair"
  | O_pr1 -> "pr1"
  | O_pr2 -> "pr2"
  | O_total -> "total"
  | O_pt -> "pt"
  | O_pt_r -> "pt_r"
  | O_tt -> "tt"
  | O_coprod -> "coprod"
  | O_ii1 -> "ii1"
  | O_ii2 -> "ii2"
  | O_sum -> "sum"
  | O_empty -> "empty"
  | O_empty_r -> "empty_r"
  | O_c -> "c"
  | O_ic_r -> "ic_r"
  | O_ic -> "ic"
  | O_paths -> "paths"
  | O_refl -> "refl"
  | O_J -> "J"
  | O_rr0 -> "rr0"
  | O_rr1 -> "rr1"

let oheads = [ O_u; O_j; O_ev; O_lambda; O_forall; O_pair; O_pr1; O_pr2;
  O_total; O_pt; O_pt_r; O_tt; O_coprod; O_ii1; O_ii2; O_sum; O_empty;
  O_empty_r; O_c; O_ic_r; O_ic; O_paths; O_refl; O_J; O_rr0; O_rr1 ]

(** Heads for inference rules. *)
type ruleHead =
  | Rule of int * string		(* the number of the rule in the paper, together with a convenient name *)

let rulehead_to_string = function
  | Rule (n,s) -> s

(** Source code positions. *)

type 'a marked = position * 'a
let strip_pos ((_:position), x) = x
let get_pos ((pos:position), _) = pos
let with_pos (pos:position) e = (pos, e)
let with_pos_of ((pos:position),_) e = (pos,e)
let nowhere x = (Nowhere,x)

(** Variables *)

type var = var' marked
and  var' =				(* a variable in both TS and LF *)
  | Var of string
  | VarGen of int * string
  | VarUnused

let vartostring' = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | VarUnused -> "_"
let vartostring v = vartostring' (strip_pos v)

type lf_var =				(* a variable in LF *)
  | LF_Var of var'
  | LF_VarDefined of string * int         (** A definition, appearing as a variable of LF. *)

let lf_var_tostring = function
  | LF_Var v -> vartostring' v
  | LF_VarDefined (name,aspect) -> "[" ^ name ^ "." ^ (string_of_int aspect) ^ "]"

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
  | L of lf_var
  | U of uHead			(** labels for u-expressions of TS *)
  | T of tHead			(** labels for t-expressions of TS *)
  | O of oHead			(** labels for o-expressions of TS *)
  | R of ruleHead		(** names of inference rules of TS *)

let labels = List.concat [
  List.map (fun h -> U h) uheads;
  List.map (fun h -> T h) theads;
  List.map (fun h -> O h) oheads
]

let label_to_string = function
  | L v -> lf_var_tostring v
  | U h -> "[" ^ uhead_to_string h ^ "]"
  | T h -> "[" ^ thead_to_string h ^ "]"
  | O h -> "[" ^ ohead_to_string h ^ "]"
  | R h -> rulehead_to_string h

let string_to_label = List.map (fun h -> label_to_string h, h) labels
	
type atomic_term = atomic_term' marked
and atomic_term' =
  | Variable of var'
	(** A variable. *)
  | EmptyHole of int
        (** An empty hole, to be filled in later. *)
  | APPLY of label * canonical_term list
	(** Iterated function application. *)
and canonical_term = 
  | ATOMIC of atomic_term
	(** A wrapper that gives the position in the TS source code, for error messages *)
  | LAMBDA of var * canonical_term
	(** The lambda of LF. *)

type ts_expr = atomic_term

type lf_expr = canonical_term

(** Notation. *)

let ( ** ) f x = nowhere(APPLY(f,x))

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
  | F_ulevel_equality
  | F_type_uequality
  | F_type_equality
  | F_object_uequality
  | F_object_equality

type lf_type = bare_lf_type marked
and bare_lf_type =
  | F_Pi of var' * lf_type * lf_type
  | F_APPLY of tfHead * lf_expr list
  | F_Singleton of lf_expr * lf_type
  | F_hole

let tfhead_to_string = function
  | F_uexp -> "uexp"
  | F_texp -> "texp"
  | F_oexp -> "oexp"
  | F_istype -> "istype"
  | F_hastype -> "hastype"
  | F_ulevel_equality -> "uequal"
  | F_type_uequality -> "tsim"
  | F_type_equality -> "tequal"
  | F_object_uequality -> "osim"
  | F_object_equality -> "oequal"

let tfheads = [ 
  F_uexp; F_texp; F_oexp; F_istype; F_hastype; F_ulevel_equality ;
  F_type_uequality; F_type_equality; F_object_uequality; F_object_equality ]

let tfhead_strings = List.map (fun x -> tfhead_to_string x, x) tfheads


let ( *** ) f x = nowhere (F_APPLY(f,x))

let uexp = F_uexp *** []
let texp = F_texp *** []
let oexp = F_oexp *** []

let ( @> ) a b = nowhere (F_Pi(VarUnused, a, b))

let istype t = F_istype *** [t]
let hastype o t = F_hastype *** [o;t]
let ulevel_equality u u' = F_ulevel_equality *** [u;u']
let type_uequality t t' = F_type_uequality *** [t;t']
let type_equality t t' = F_type_equality *** [t;t']
let object_similariy o o' t = F_object_uequality *** [o;o';t]
let object_equality o o' t = F_object_equality *** [o;o';t]

let texp1 = oexp @> texp
let texp2 = oexp @> oexp @> texp
let texp3 = oexp @> oexp @> oexp @> texp

let oexp1 = oexp @> oexp
let oexp2 = oexp @> oexp @> oexp
let oexp3 = oexp @> oexp @> oexp @> oexp

let uhead_to_lf_type = function
  | U_next -> uexp @> uexp
  | U_max -> uexp @> uexp @> uexp

let thead_to_lf_type = function
  | T_El -> oexp @> texp
  | T_U -> uexp @> texp
  | T_Pi -> texp @> texp1 @> texp
  | T_Sigma -> texp @> texp1 @> texp
  | T_Pt -> texp
  | T_Coprod -> texp @> texp @> texp
  | T_Coprod2 -> texp @> texp @> texp1 @> texp1 @> texp
  | T_Empty -> texp
  | T_IC -> texp @> oexp @> texp1 @> texp2 @> oexp3 @> texp
  | T_Id -> texp @> oexp @> oexp @> texp

let ohead_to_lf_type = function
  | O_u -> uexp @> oexp
  | O_j -> uexp @> uexp @> oexp
  | O_ev -> oexp @> oexp @> texp1 @> oexp
  | O_lambda -> texp @> oexp1 @> oexp
  | O_forall -> uexp @> uexp @> oexp @> oexp1 @> oexp
  | O_pair -> oexp @> oexp @> texp1 @> oexp
  | O_pr1 -> texp @> texp1 @> oexp @> oexp
  | O_pr2 -> texp @> texp1 @> oexp @> oexp
  | O_total -> uexp @> uexp @> oexp @> oexp1 @> oexp
  | O_pt -> oexp
  | O_pt_r -> oexp @> texp1 @> oexp
  | O_tt -> oexp
  | O_coprod -> uexp @> uexp @> oexp @> oexp @> oexp
  | O_ii1 -> texp @> texp @> oexp @> oexp
  | O_ii2 -> texp @> texp @> oexp @> oexp
  | O_sum -> texp @> texp @> oexp @> oexp @> oexp @> texp1 @> oexp
  | O_empty -> oexp
  | O_empty_r -> texp @> oexp @> oexp
  | O_c -> texp @> oexp @> texp1 @> texp2 @> oexp3 @> oexp @> oexp @> oexp
  | O_ic_r -> texp @> oexp @> texp1 @> texp2 @> oexp3 @> oexp @> texp2 @> oexp @> oexp
  | O_ic -> oexp @> oexp @> oexp1 @> oexp2 @> oexp3 @> oexp
  | O_paths -> texp @> oexp @> oexp @> oexp
  | O_refl -> texp @> oexp @> oexp
  | O_J -> texp @> oexp @> oexp @> oexp @> oexp @> texp2 @> oexp
  | O_rr0 -> uexp @> uexp @> oexp @> oexp @> oexp @> oexp
  | O_rr1 -> uexp @> oexp @> oexp @> oexp

type vardist = int list list
let head_to_vardist = function
  | T T_Coprod2 -> Some (2, [] :: [] :: [0] :: [1] :: [])
  | O O_ic_r -> Some (5, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [] :: [3;4] :: [] :: [])
  | T T_IC -> Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [])
  | O O_ev -> Some (1, [] :: [] :: [0] :: [])
  | T T_Pi | T T_Sigma | O O_lambda -> Some (1, [] :: [0] :: [])
  | O O_forall -> Some (1, [] :: [] :: [] :: [0] :: [])
  | O O_pair -> Some (1, [] :: [] :: [0] :: [])
  | O O_pr1 | O O_pr2 -> Some (1, [] :: [0] :: [] :: [])
  | O O_total -> Some (1, [] :: [] :: [] :: [0] :: [])
  | O O_pt_r -> Some (1, [] :: [0] :: [])
  | O O_c -> Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [] :: [] :: [])
  | O O_ic -> Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: [])
  | O O_J -> Some (2, [] :: [] :: [] :: [] :: [] :: [0;1] :: [])
  | _ -> None

(** The derivation rules of TS. 

    The list of rules is part of the LF signature, giving LF types for LF term constants. *)
let rules = ref []

let label_to_lf_type env = function
  | U h -> uhead_to_lf_type h
  | T h -> thead_to_lf_type h
  | O h -> ohead_to_lf_type h
  | R h -> List.assoc h !rules
  | L v -> List.assoc v env

(*** The "kinds" of LF. 

    Notation: constructors starting with "K_" refer to kinds of LF. *)
type lfkind =
  | K_type
  | K_Pi of var' * lf_type * lfkind

let ( @@> ) a b = K_Pi(VarUnused, a, b)

let tfhead_to_kind = function
  | F_uexp -> K_type
  | F_texp -> K_type
  | F_oexp -> K_type
  | F_istype -> texp @@> K_type
  | F_hastype -> oexp @@> texp @@> K_type
  | F_ulevel_equality -> uexp @@> uexp @@> K_type
  | F_type_uequality -> texp @@> texp @@> K_type
  | F_type_equality -> texp @@> texp @@> K_type
  | F_object_uequality -> oexp @@> oexp @@> texp @@> K_type
  | F_object_equality -> oexp @@> oexp @@> texp @@> K_type

type oSubs = (var' * ts_expr) list

(*** Contexts. *)

type environment_type = (lf_var * lf_type) list

let environment : environment_type ref = ref []

let def_bind name aspect o t env = (LF_VarDefined(name,aspect), F_Singleton(o,t)) :: env

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr; 
    if !genctr < 0 then raise GensymCounterOverflow;
    VarGen (!genctr, x)) in
  fun v -> match v with 
  | Var x | VarGen(_,x) -> newgen x
  | VarUnused as v -> v

let ts_bind' (v,t) env = match v with
  | VarUnused -> env
  | v -> 
      (LF_Var (newfresh (Var "hast")), hastype (ATOMIC (nowhere (Variable v))) t) :: 
      (LF_Var v,oexp) :: 
      env

let ts_bind (v,t) env = ts_bind' (strip_pos v, t) env

let new_hole' = 
  let counter = ref 0 in
  function () -> (
    let h = EmptyHole !counter in
    incr counter;
    h)
let new_hole () = nowhere (new_hole' ())

exception Internal_expr of lf_expr
exception Unimplemented_expr of lf_expr

(* 
  Local Variables:
  compile-command: "ocamlbuild typesystem.cmo "
  End:
 *)
