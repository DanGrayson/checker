(** Voevodsky's type system TS mixed with the type system LF of Logical Frameworks (Edinburgh style).

@author Dan Grayson

    *)

(**

This file encodes the type system TS developed in the paper {i A universe
polymorphic type system}, by Vladimir Voevodsky, the version dated October,
2012.

  *)

open Error

(** Variables *)
let strip_pos_var : position * 'a -> 'a = snd
let get_pos_var : position * 'a -> position = fst

(** Object variable, probably obsolete. *)
type var = position * var'
and var' =
    Var of string
  | VarGen of int * string
  | VarUnused

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
 *)

(** The various labels for u-expressions of TS. *)
type uHead =
  | U_plus of int
	(** A pair [(M,n)], denoting [M+n], the n-th successor of [M].  Here [n] should be nonnegative *)
  | U_max
	(** A pair [(M,M')] denoting [max(M,M')]. *)

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

      (** The type [label] corresponds to the constant atomic terms of LF. 

	  For definitions, we envision multiple aspects.  For example, aspect 1
	  could be a t-expression T and aspect 2 could be a derivation of the
	  judgment that T is a type.  Or aspect 1 could be an o-expression t,
	  aspect 2 could be a type T, and aspect 3 could be a derivation of the
	  judgment that t has type T.  Similarly for the other two types of
	  judgment in TS.
       *)
type label =
  | U of uHead			(** labels for u-expressions of TS *)
  | T of tHead			(** labels for t-expressions of TS *)
  | O of oHead			(** labels for o-expressions of TS *)
  | Defapp of string * int	(** application of an aspect of a definition *)
	
(** The type [expr] corresponds to the canonical terms of LF. *)
type expr = 
  | POS of position * bare_expr
	(** A wrapper that gives the position in the TS source code, for error messages *)
  | LAMBDA of var * expr
	(** The lambda of LF. *)

	(** The type [bare_expr] corresponds to the atomic terms of LF.  
									 
	    APPLY is the iterated function application of LF, and all of its
	    arguments must be there (so this is the "eta-long" form).  Thus
	    instead of writing [((((f a) b) c) d)] we write
	    [APPLY(f,\[a;b;c;d\])], where [f] is a variable or a constant.
	    Both aspects offer advantages for pattern matching.  One slight
	    disadvantage is that a constant [f] appearing as a term is encoded
	    as [APPLY(f,\[\])], which represents the redundant application of
	    [f] to zero arguments.

	    Remark: eta-expansion is type driven, so that if it is desired to
	    derive [ f : A -> B ], and [f] is not already a lambda, we "reduce"
	    to deriving [ (LAMBDA x, f x) : A -> B ].  That's also why don't
	    decorate the [LAMBDA] with the type, as in [ LAMBDA x:A, f x ],
	    because it would just get in the way.*)
and bare_expr =
  | Variable of var'
	(** A variable. *)
  | EmptyHole of int
        (** An empty hole, to be filled in later.

	    All holes are numbered with a serial number, so copies share the
	    same identity.
	 *)
  | APPLY of label * expr list
	(** Iterated function application. *)

	(** The following constants for LF type families segregate TS
	    expressions into three forms: u-expressions, t-expressions, and
	    o-expressions, and they introduce the four forms of judgments. *)
type tfHead =
  | F_uexp
  | F_texp
  | F_oexp
  | F_Is_type
  | F_Has_type
  | F_Type_equality
  | F_Object_equality

type canonical_type_family =
  | F_Pi of var' * canonical_type_family * canonical_type_family
  | F_APPLY of tfHead * expr list
  | F_Hole

let ( ** ) f x = F_APPLY(f,x)
let hole = F_Hole
let uexp = F_uexp ** []
let texp = F_texp ** []
let oexp = F_oexp ** []
let ( @> ) a b = F_Pi(VarUnused, a, b)
let istype t = F_Is_type ** [t]
let hastype o t = F_Has_type ** [o;t]
let type_equality t t' = F_Type_equality ** [t;t']
let object_equality o o' t = F_Object_equality ** [o;o';t]

let texp1 = oexp @> texp
let texp2 = oexp @> oexp @> texp
let texp3 = oexp @> oexp @> oexp @> texp
let oexp1 = oexp @> oexp
let oexp2 = oexp @> oexp @> oexp
let oexp3 = oexp @> oexp @> oexp @> oexp
let type_families = [
       T T_El, oexp  @> texp;
        T T_U, uexp  @> texp;
       T T_Pi, texp  @> texp1 @> texp;
    T T_Sigma, texp  @> texp1 @> texp;
       T T_Pt, texp;
   T T_Coprod, texp  @> texp  @> texp;
  T T_Coprod2, texp  @> texp  @> texp1 @> texp1 @> texp;
    T T_Empty, texp;
       T T_IC, texp  @> oexp  @> texp1 @> texp2 @> oexp3 @> texp;
       T T_Id, texp  @> oexp  @> oexp  @> texp;
        O O_u, uexp  @> oexp;
        O O_j, uexp  @> uexp  @> oexp;
       O O_ev, oexp  @> oexp  @> texp1 @> oexp;
   O O_lambda, texp  @> oexp1 @> oexp;
   O O_forall, texp  @> texp1 @> texp;
     O O_pair, oexp  @> oexp  @> texp1 @> oexp;
      O O_pr1, texp  @> texp1 @> oexp  @> oexp;
      O O_pr2, texp  @> texp1 @> oexp  @> oexp;
    O O_total, uexp  @> uexp  @> oexp  @> oexp1 @> oexp;
       O O_pt, oexp;
     O O_pt_r, oexp  @> texp1 @> oexp;
       O O_tt, oexp;
   O O_coprod, uexp  @> uexp  @> oexp  @> oexp  @> oexp;
      O O_ii1, texp  @> texp  @> oexp  @> oexp;
      O O_ii2, texp  @> texp  @> oexp  @> oexp;
      O O_sum, texp  @> texp  @> oexp  @> oexp  @> oexp  @> texp1 @> oexp;
    O O_empty, oexp;
  O O_empty_r, texp  @> oexp  @> oexp;
        O O_c, texp  @> oexp  @> texp1 @> texp2 @> oexp3 @> oexp  @> oexp  @> oexp;
     O O_ic_r, texp  @> oexp  @> texp1 @> texp2 @> oexp3 @> oexp  @> texp2 @> oexp  @> oexp;
       O O_ic, oexp  @> oexp  @> oexp1 @> oexp2 @> oexp3 @> oexp;
    O O_paths, texp  @> oexp  @> oexp  @> oexp;
     O O_refl, texp  @> oexp  @> oexp;
        O O_J, texp  @> oexp  @> oexp  @> oexp  @> oexp  @> texp2 @> oexp;
      O O_rr0, uexp  @> uexp  @> oexp  @> oexp  @> oexp  @> oexp;
      O O_rr1, uexp  @> oexp  @> oexp  @> oexp;
];

type kind =
  | K_type
  | K_Pi of var' * canonical_type_family * kind

let ( @@> ) a b = K_Pi(VarUnused, a, b)

let kinds = [
             F_uexp, K_type;
             F_texp, K_type;
             F_oexp, K_type;
          F_Is_type, texp @@> K_type;
         F_Has_type, oexp @@> texp @@> K_type;
    F_Type_equality, texp @@> texp @@> K_type;
  F_Object_equality, oexp @@> texp @@> texp @@> K_type;
]

let rec get_u = function
  | POS (_,(Variable _ | APPLY(U _,_) as u)) -> u
  | _ -> raise Error.Internal

let with_pos pos e = POS (pos, e)
let strip_pos = function
  | POS(_,x) -> x
  | _ -> raise Error.Internal
let get_pos = function
  | POS(pos,_) -> pos
  | _ -> Error.Nowhere
let with_pos_of x e = POS (get_pos x, e)
let nowhere x = with_pos Error.Nowhere x
let new_hole' = 
  let counter = ref 0 in
  function () -> (
    let h = EmptyHole !counter in
    incr counter;
    h)
let new_hole () = nowhere (new_hole' ())

(** 
    A universe context [UC = (Fu,A)] is represented by a list of universe variables [Fu] and a list of
    equations [M_i = N_i] between two u-level expressions formed from the variables in [Fu]
    that defines the admissible subset [A] of the functions [Fu -> nat].  It's just the subset
    that matters.
 *) 
type uContext = UContext of var' list * (expr * expr) list
let emptyUContext = UContext ([],[])
let mergeUContext : uContext -> uContext -> uContext =
  function UContext(uvars,eqns) -> function UContext(uvars',eqns') -> UContext(List.rev_append uvars' uvars,List.rev_append eqns' eqns)

(** t-context; a list of t-variables declared as "Type". *)
type tContext = var' list
let emptyTContext : tContext = []

type utContext = uContext * tContext
let emptyUTContext = emptyUContext, emptyTContext

(** o-context; a list of o-variables with T-expressions representing their declared type. *)
type oContext = (var' * expr) list				  (* [Gamma] *)
let emptyOContext : oContext = []

type oSubs = (var' * expr) list

(** Definitions. *)

type identifier = Ident of string
type definition = (int * expr * canonical_type_family) list
type vartype = Ulevel_variable | Type_variable | Object_variable | Def_variable

(** Contexts. *)

type environment_type = {
    uc : uContext;
    tc : tContext;
    oc : oContext;
    definitions : (identifier * definition) list;
    lookup_order : (string * (var' * vartype)) list
  }

let obind' (v,t) env = match v with
    Var name -> { env with oc = (v,t) :: env.oc; lookup_order = (name, (v, Object_variable)) :: env.lookup_order }
  | VarGen (_,_) -> { env with oc = (v,t) :: env.oc }
  | VarUnused -> env

let obind (v,t) env = obind' (strip_pos_var v, t) env

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr; 
    if !genctr < 0 then raise Error.GensymCounterOverflow;
    VarGen (!genctr, x)) in
  fun v -> match v with 
      Var x | VarGen(_,x) -> newgen x
    | VarUnused as v -> v

(*
  Local Variables:
  compile-command: "ocamlbuild typesystem.cmo "
  End:
 *)
