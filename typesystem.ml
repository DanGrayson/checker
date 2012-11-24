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
  | UU_plus of int
	(** A pair [(M,n)], denoting [M+n], the n-th successor of [M].  Here [n] should be nonnegative *)
  | UU_max
	(** A pair [(M,M')] denoting [max(M,M')]. *)

(** The various labels for t-expressions of TS. *)
type tHead =
	(* TS0: *)
  | TT_El
      (** [T_El]; converts an object term into the corresponding type term *)
  | TT_U
      (** [T_U m]; a u-level expression, as a type *)
  | TT_Pi
      (** [T_Pi(T,(x,T')) <--> \[Pi;x\](T,T')] *)
      (* TS1: *)
  | TT_Sigma
      (** [T_Sigma(T,(x,T')) <--> \[Sigma;x\](T,T')] *)
      (* TS2: *)
  | TT_Pt
      (** Corresponds to [Pt]() in the paper; the unit type *)
      (* TS3: *)
  | TT_Coprod
  | TT_Coprod2
      (* TS4: *)
  | TT_Empty
      (** The empty type.  
	  
	  Voevodsky doesn't list this explicitly in the definition of TS4, but it gets used in derivation rules, so I added it.
	  Perhaps he intended to write [\[T_El\](\[empty\]())] for it. *)
      (* TS5: *)
  | TT_IC
	(** [T_IC(A,a,(x,B),(x,(y,D)),(x,(y,(z,q)))) <--> \[IC;x,y,z\](A,a,B,D,q)] *)
      (* TS6: *)
  | TT_Id
      (** Identity type; paths type. *)
      (* TS7: *)
      (* end of TS *)

(** The various labels for o-expressions of TS. *)
type oHead =
    (* TS0: *)
  | OO_u
	(** [u]; universe as an object. *)
  | OO_j
	(** [j](U,U') *)
  | OO_ev
	(** [O_ev(f,o,(x,T)) <--> \[ev;x\](f,o,T)]
	    
	    Application of the function [f] to the argument [o].
	    
	    Here [T], with the type of [o] replacing [x], gives the type of the result.

	    By definition, such subexpressions [T] are not essential.
	 *)
  | OO_lambda
	(** [O_lambda(T,(x,o)) <--> \[lambda;x\](T,o)] *)
  | OO_forall
	(** [O_forall(M,M',o,(x,o')) <--> \[forall;x\]([M],[M'],o,o')]
	    
	    [O_forall] is the object term corresponding to [Pi].
	    The type of the term is given by the max of the two u-levels. *)
      (* TS1: *)
  | OO_pair
	(** [O_pair(a,b,(x,T)) <--> \[pair;x\](a,b,T)]
	    
	    An instance of [Sigma]. *)
  | OO_pr1
	(** [O_pr1(T,(x,T'),o) <--> \[pr1;x\](T,T',o)] 

	    By definition, such subexpressions [T] are not essential.
	 *)
  | OO_pr2
	(** [O_pr2(T,(x,T'),o) <--> \[pr2;x\](T,T',o)] 

	    By definition, such subexpressions [T] are not essential.
	 *)
  | OO_total
	(** [O_total(m1,m2,o1,(x,o2)) <--> \[total;x\](m1,m2,o1,o2)]

	    Corresponds to [total] or [prod] in the paper. *)
	(* TS2: *)
  | OO_pt
      (** Corresponds to [\[pt\]] in the paper. *)
  | OO_pt_r
	(** [O_pt_r(o,(x,T)) <--> \[pt_r;x\](o,T)]
	    
	    [O_pt_r] is the eliminator for [Pt]. *)
  | OO_tt
      (** [O_tt <--> \[tt\]()]
	  
	  [O_tt] is the unique instance of the unit type [Pt]. *)
      (* TS3: *)
  | OO_coprod
	(** The type of the term is given by the [max] of the two u-levels. *)
  | OO_ii1
	(** The type of a term [O_ii1(T,T',o)] is [Coprod(T,T')]; here [o] has type [T] *)
  | OO_ii2
	(** The type of a term [O_ii2(T,T',o)] is [Coprod(T,T')]; here [o] has type [T'] *)
  | OO_sum
	(** The type of a term [O_sum(T,T',s,s',o,(x,S))] is [S], with [x] replaced by [o]. *)
	(* TS4: *)
  | OO_empty
      (** [ O_empty <--> \[empty\]() ]
				    
	  The type of [\[empty\]] is the smallest universe, [uuu0]. 

	  Remember to make [El]([empty]()) reduce to [Empty]().
       *)
  | OO_empty_r
	(** The elimination rule for the empty type.

	    The type of [O_empty_r(T,o)] is [T].  Here the type of [o] is [Empty], the empty type. *)
  | OO_c
	(** Corresponds to [c] in the paper. *)
  | OO_ic_r
	(** [ic_r] is the elimination rule for inductive types (generalized W-types) *)
  | OO_ic
	(** Corresponds to [ic].  Its type is the max of the three u-level expressions. *)
	(* TS6: *)
  | OO_paths
	(** The object corresponding to the identity type [Id].  

	    Its type is the type corresponding to the given universe level. *)
  | OO_refl
	(** Reflexivity, or the constant path. 
	    
	    The type of [O_refl(T,o)] is [Id(T,o,o)]. *)
  | OO_J
	(** The elimination rule for Id; Id-elim. *)
      (* TS7: *)
  | OO_rr0
	(** Resizing rule.

	    The type of [O_rr0(M_2,M_1,s,t,e)] is [U(M_1)], resized downward from [U M_2].

	    By definition, the subexpressions [t] and [e] are not essential.
	 *)
  | OO_rr1
	(** Resizing rule.

	    The type of [O_rr1(M,a,p)] is [U uuu0], resized downward from [U M].

	    By definition, the subexpression [p] is not essential.
	 *)
      (* end of TS *)

	(** The type [label] corresponds to the constant atomic terms of LF. *)
type label =
  | UU of uHead
  | TT of tHead
  | OO of oHead
  | Defapp of string			(* application of a definition *)
	
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
  | EmptyHole
        (** An empty hole, to be filled in later. *)
  | APPLY of label * expr list
	(** Iterated function application. *)

	(** The following constants for LF type families segregate TS
	    expressions into three forms: u-expressions, t-expressions, and
	    o-expressions, and they introduce the four forms of judgments. *)
type tfHead =
  | TF_Ulevel
  | TF_Type
  | TF_Object
  | TF_Is_type
  | TF_Has_type
  | TF_Type_equality
  | TF_Object_equality

type canonical_type_family =
  | ATOMIC of atomic_type_family
  | TF_Pi of var' * canonical_type_family * canonical_type_family
and atomic_type_family =
  | TF_APPLY of tfHead * canonical_type_family list

let ulevel_TF = ATOMIC (TF_APPLY(TF_Ulevel,[]))
let type_TF   = ATOMIC (TF_APPLY(TF_Type  ,[]))
let obj_TF    = ATOMIC (TF_APPLY(TF_Object,[]))

let arrow_T a b = TF_Pi(VarUnused, a, b)

type kind =
  | TYPE_KIND
  | PI_KIND of var' * canonical_type_family * kind

let type_K = TYPE_KIND

let arrow_K a k = PI_KIND(VarUnused, a, k)

let ohead_to_kind = function
  | OO_ev -> arrow_K obj_TF (arrow_K obj_TF (arrow_K (arrow_T obj_TF type_TF) type_K))
  | _ -> raise Error.NotImplemented

let rec get_u = function
  | POS (_,(Variable _ | APPLY(UU _,_) as u)) -> u
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

(* Abbreviations, conventions, and definitions; from the paper *)

type identifier = Ident of string
type definition = 
  | TDefinition   of identifier * ((uContext * tContext * oContext)         * expr)
  | ODefinition   of identifier * ((uContext * tContext * oContext) * expr * expr)
  | TeqDefinition of identifier * ((uContext * tContext * oContext)         * expr * expr)
  | OeqDefinition of identifier * ((uContext * tContext * oContext) * expr * expr * expr)

type vartype = Ulevel_variable | Type_variable | Object_variable

type environment_type = {
    uc : uContext;
    tc : tContext;
    oc : oContext;
    definitions : (identifier * definition) list;
    lookup_order : (string * (var' * vartype)) list	(* put definitions in here later *)
  }

let obind' (v,t) env = match v with
    Var name -> { env with oc = (v,t) :: env.oc; lookup_order = (name, (v, Object_variable)) :: env.lookup_order }
  | VarGen (_,_) -> { env with oc = (v,t) :: env.oc }
  | VarUnused -> env

let obind (v,t) env = obind' (strip_pos_var v, t) env

(*
  Local Variables:
  compile-command: "ocamlbuild typesystem.cmo "
  End:
 *)
