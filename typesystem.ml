(** Voevodsky's type system TS

@author Dan Grayson

    *)

(**

This file encodes the type system TS developed in the paper {i A universe
polymorphic type system}, by Vladimir Voevodsky, the version dated October,
2012.

  *)

let debug_mode = ref false

type position =
  | Position of Lexing.position * Lexing.position (** start, end *)
  | Nowhere
let error_format_pos = function
  | Position(p,q) 
    -> "File \"" ^ p.Lexing.pos_fname ^ "\", " 
      ^ (if p.Lexing.pos_lnum = q.Lexing.pos_lnum
	 then "line " ^ (string_of_int p.Lexing.pos_lnum) 
	 else "lines " ^ (string_of_int p.Lexing.pos_lnum) ^ "-" ^ (string_of_int q.Lexing.pos_lnum))
      ^ ", " 
      ^ (let i = p.Lexing.pos_cnum-p.Lexing.pos_bol+1
         and j = q.Lexing.pos_cnum-q.Lexing.pos_bol in
         if i = j
	 then "character " ^ (string_of_int i)
         else "characters " ^ (string_of_int i) ^ "-" ^ (string_of_int j))
  | Nowhere -> "nowhere:0:0"

let nowhere x = (Nowhere,x)
let strip_pos : position * 'a -> 'a = snd
let get_pos : position * 'a -> position = fst
let with_pos (p:position) b = (p, b)
let with_pos_of a b = (get_pos a, b)

exception TypingError of position * string
exception TypingUnimplemented of position * string
exception GeneralError of string
exception GensymCounterOverflow
exception NotImplemented
exception Unimplemented of string
exception InternalError
exception VariableNotInContext
exception NoMatchingRule
exception Eof

(** Object variable. *)
type oVar = position * oVar'
and oVar' =
    OVar of string
  | OVarGen of int * string
  | OVarUnused
  | OVarEmptyHole
let make_oVar c = OVar c

let fresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr; 
    if !genctr < 0 then raise GensymCounterOverflow;
    OVarGen (!genctr, x)) in
  fun v -> match strip_pos v with 
      OVar x | OVarGen(_,x) -> newgen x
    | OVarUnused as v -> v
    | OVarEmptyHole as v -> v

(** Type variable. *)
type tVar = position * tVar'
and tVar' = TVar of string
let make_tVar c = TVar c

(** Universe variable. *)
type uVar = position * uVar'
and uVar' = UVar of string
let make_uVar c = UVar c

(*


*)

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
    The type [uExpr] implements all aspects of judging that we have a valid
    uExpr, except for possibly constraining the list of variables used to members
    of a given list.
 *)
type uExpr = position * uExpr'
and uExpr' =
  | Uvariable of uVar'
	(** A u-level variable. *)
  | Uplus of uExpr * int
	(** A pair [(M,n)], denoting [M+n], the n-th successor of [M].  Here [n] should be nonnegative *)
  | Umax of uExpr * uExpr
	(** A pair [(M,M')] denoting [max(M,M')]. *)
  | UEmptyHole
        (** A u-level, to be filled in later, by type checking. *)
  | UNumberedEmptyHole of int
        (** A u-level, to be filled in later, by type checking. *)
  | U_def of string * uExpr list

let uuu0 = nowhere(Uvariable (UVar "uuu0"))

type  oBinding = oVar * oExpr
and   tBinding = oVar * tExpr
and   tBinding2= oVar * oVar  * tExpr
and  toBinding = oVar * tExpr * oBinding
and  ooBinding = oVar * oExpr * oBinding
and ttoBinding = oVar * tExpr * toBinding
and oooBinding = oVar * oExpr * ooBinding

(** [tExpr] is the type of T-expressions. *)
and tExpr = position * tExpr'
and tExpr' =
  (* TS0 *)
  | T_EmptyHole
        (** a hole to be filled in later  *)
  | T_NumberedEmptyHole of int
        (** A hole to be filled in later, by type checking. *)
  | T_variable of tVar'
  | T_El of oExpr
	(** [T_El]; converts an object term into the corresponding type term *)
  | T_U of uExpr
	(** [T_U m]; a u-level expression, as a type *)
  | T_Pi of tExpr * tBinding
	(** [T_Pi(T,(x,T')) <--> \[Pi;x\](T,T')] *)
    (* TS1 *)
  | T_Sigma of tExpr * tBinding
	(** [T_Sigma(T,(x,T')) <--> \[Sigma;x\](T,T')] *)
    (* TS2 *)
  | T_Pt
      (** Corresponds to [Pt]() in the paper; the unit type *)
    (* TS3 *)
  | T_Coprod of tExpr * tExpr
  | T_Coprod2 of tExpr * tExpr * tBinding * tBinding * oExpr
      (* TS4 *)
  | T_Empty
      (** The empty type.  
	  
	  Voevodsky doesn't list this explicitly in the definition of TS4, but it gets used in derivation rules, so I added it.
	  Perhaps he intended to write [\[T_El\](\[empty\]())] for it. *)
      (* TS5 *)
  | T_IC of tExpr * oExpr * ttoBinding
	(** [T_IC(A,a,(x,B,(y,D,(z,q)))) <--> \[IC;x,y,z\](A,a,B,D,q)]
	 *)
      (* TS6 *)
  | T_Id of tExpr * oExpr * oExpr
      (** Identity type; paths type. *)
      (* TS7 *)
  | T_def of string * uExpr list * tExpr list * oExpr list
  | T_nat
      (** nat 

	  The type of natural numbers. *)
      
(** [oExpr] is the type of o-expressions. *)
and oExpr = position * oExpr'
and oExpr' =
    (* TS0 *)
  | O_emptyHole
        (** a hole to be filled in later *)
  | O_numberedEmptyHole of int
        (** A hole to be filled in later, by type checking. *)
  | O_variable of oVar'
	(** An o-variable. *)
  | O_u of uExpr
	(** [u]; universe as an object. *)
  | O_j of uExpr * uExpr
	(** [j](U,U') *)
  | O_ev of oExpr * oExpr * tBinding
	(** [O_ev(f,o,(x,T)) <--> \[ev;x\](f,o,T)]
	    
	    Application of the function [f] to the argument [o].
	    
	    Here [T], with the type of [o] replacing [x], gives the type of the result.

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_lambda of tExpr * oBinding
	(** [O_lambda(T,(x,o)) <--> \[lambda;x\](T,o)] *)
  | O_forall of uExpr * uExpr * oExpr * oBinding
	(** [O_forall(M,M',o,(x,o')) <--> \[forall;x\]([M],[M'],o,o')]
	    
	    [O_forall] is the object term corresponding to [Pi].
	    The type of the term is given by the max of the two u-levels. *)
	(* TS1 *)
  | O_pair of oExpr * oExpr * tBinding
	(** [O_pair(a,b,(x,T)) <--> \[pair;x\](a,b,T)]
	    
	    An instance of [Sigma]. *)
  | O_pr1 of tExpr * tBinding * oExpr
	(** [O_pr1(T,(x,T'),o) <--> \[pr1;x\](T,T',o)] 

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_pr2 of tExpr * tBinding * oExpr
	(** [O_pr2(T,(x,T'),o) <--> \[pr2;x\](T,T',o)] 

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_total of uExpr * uExpr * oExpr * oBinding
	(** [O_total(m1,m2,o1,(x,o2)) <--> \[total;x\](m1,m2,o1,o2)]

	    Corresponds to [total] or [prod] in the paper. *)
	(* TS2 *)
  | O_pt
      (** Corresponds to [\[pt\]] in the paper. *)
      
  | O_pt_r of oExpr * tBinding
	(** [O_pt_r(o,(x,T)) <--> \[pt_r;x\](o,T)]
	    
	    [O_pt_r] is the eliminator for [Pt]. *)
  | O_tt
      (** [O_tt <--> \[tt\]()]
	  
	  [O_tt] is the unique instance of the unit type [Pt]. *)
      (* TS3 *)
  | O_coprod of uExpr * uExpr * oExpr * oExpr
	(** The type of the term is given by the [max] of the two u-levels. *)
  | O_ii1 of tExpr * tExpr * oExpr
	(** The type of a term [O_ii1(T,T',o)] is [Coprod(T,T')]; here [o] has type [T] *)
  | O_ii2 of tExpr * tExpr * oExpr
	(** The type of a term [O_ii2(T,T',o)] is [Coprod(T,T')]; here [o] has type [T'] *)
  | O_sum of tExpr * tExpr * oExpr * oExpr * oExpr * tBinding
	(** The type of a term [O_sum(T,T',s,s',o,(x,S))] is [S], with [x] replaced by [o]. *)
	(* TS4 *)
  | O_empty
      (** [ O_empty <--> \[empty\]() ]
				    
	  The type of [\[empty\]] is the smallest universe, [uuu0]. 

	  Remember to make [El]([empty]()) reduce to [Empty]().
       *)
  | O_empty_r of tExpr * oExpr
	(** The elimnination rule for the empty type.

	    The type of [O_empty_r(T,o)] is [T].  Here the type of [o] is [Empty], the empty type. *)
  | O_c of tExpr * oExpr * ttoBinding * oExpr * oExpr
	(** [O_c(A,a,(x,B,(y,D,(z,q))),b,f) <--> \[c;x,y,z\](A,a,B,D,q,b,f)]
	    
	    Corresponds to [c] in the paper. *)
  | O_ic_r of tExpr * oExpr * ttoBinding * oExpr * tBinding2 * oExpr
	(** [O_ic_r(A,a,(x,B,(y,D,(z,q))),i,(x',v,S),t) <--> \[ic_r;x,y,z,x',v\](A,a,B,D,q,i,S,t)]
	    
	    ic_r is the elimination rule for inductive types (generalized W-types) *)
  | O_ic of uExpr * uExpr * uExpr * oExpr * oExpr * oooBinding
	(** [O_ic(M1,M2,M3,oA,a,(x,oB,(y,oD,(z,q)))) <--> \[[ic;x,y,z](M1,M2,M3,oA,a,oB,oD,q)\]]
	    
	    Corresponds to [ic].  Its type is the max of the three u-level expressions. *)
	(* TS6 *)
  | O_paths of uExpr * oExpr * oExpr * oExpr
	(** The object corresponding to the identity type [Id].  

	    Its type is the type corresponding to the given universe level. *)
  | O_refl of tExpr * oExpr
	(** Reflexivity, or the constant path. 
	    
	    The type of [O_refl(T,o)] is [Id(T,o,o)]. *)
  | O_J of tExpr * oExpr * oExpr * oExpr * oExpr * tBinding2
	(** The elimination rule for Id; Id-elim.

	    The type of [O_J(T,a,b,q,i,(x,e,S))] is [S\[b/x,i/e\]]. *)
      (* TS7 *)
  | O_rr0 of uExpr * uExpr * oExpr * oExpr * oExpr
	(** Resizing rule.

	    The type of [O_rr0(M_2,M_1,s,t,e)] is [U(M_1)], resized downward from [U M_2].

	    By definition, the subexpressions [t] and [e] are not essential.
	 *)
  | O_rr1 of uExpr * oExpr * oExpr
	(** Resizing rule.

	    The type of [O_rr1(M,a,p)] is [U uuu0], resized downward from [U M].

	    By definition, the subexpression [p] is not essential.
	 *)
  | O_def of string * uExpr list * tExpr list * oExpr list
  | O_numeral of int 
         (** A numeral.
	     
	     We add this variant temporarily to experiment with parsing
	     conflicts, when numerals such as 4, can be considered either as
	     o-expressions (S(S(S(S O)))) or as universe levels.  *)

(** 
    A universe context [UC = (Fu,A)] is represented by a list of universe variables [Fu] and a list of
    equations [M_i = N_i] between two u-level expressions formed from the variables in [Fu]
    that defines the admissible subset [A] of the functions [Fu -> nat].  It's just the subset
    that matters.
 *) 
type uContext = UContext of uVar' list * (uExpr * uExpr) list
let emptyUContext = UContext ([],[])
let mergeUContext : uContext -> uContext -> uContext =
  function UContext(uvars,eqns) -> function UContext(uvars',eqns') -> UContext(List.rev_append uvars' uvars,List.rev_append eqns' eqns)

(** t-context; a list of t-variables declared as "Type". *)
type tContext = tVar' list
let emptyTContext : tContext = []

type utContext = uContext * tContext
let emptyUTContext = emptyUContext, emptyTContext

(** o-context; a list of o-variables with T-expressions representing their declared type. *)
type oContext = (oVar' * tExpr) list				  (* [Gamma] *)
let emptyOContext : oContext = []

type oSubs = (oVar' * oExpr) list

(* Abbreviations, conventions, and definitions; from the paper *)

type identifier = Ident of string
type definition = 
  | TDefinition   of identifier * ((uContext * tContext * oContext)         * tExpr)
  | ODefinition   of identifier * ((uContext * tContext * oContext) * oExpr * tExpr)
  | TeqDefinition of identifier * ((uContext * tContext * oContext)         * tExpr * tExpr)
  | OeqDefinition of identifier * ((uContext * tContext * oContext) * oExpr * oExpr * tExpr)


(** Variable.

    We need the following definition, because u-variables, t-variables, and o-variables are in the same name space,
    and so we need to store them in the same look-up list. *)
type var = U of uVar' | T of tVar' | O of oVar'

type environment_type = {
    uc : uContext;
    tc : tContext;
    oc : oContext;
    definitions : (identifier * definition) list;
    lookup_order : (string * var) list	(* put definitions in here later *)
  }

let obind (v,t) env = match v with
    OVar name -> { env with oc = (v,t) :: env.oc; lookup_order = (name, O v) :: env.lookup_order }
  | OVarGen (_,_) -> { env with oc = (v,t) :: env.oc }
  | OVarUnused -> env
  | OVarEmptyHole -> env
