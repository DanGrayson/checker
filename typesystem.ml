(**

Type system TS

@author Dan Grayson

    *)

(**

This file encodes the type system TS developed in the paper {i A universe
polymorphic type system}, by Vladimir Voevodsky, the version dated October,
2012.

  *)

open Basic

(** Object variable. *)
type oVar = 
    OVar of string
  | OVarGen of int * string
  | OVarDummy

let fresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr; 
    if !genctr < 0 then raise GensymCounterOverflow;
    OVarGen (!genctr, x)) in
  function
      OVar x | OVarGen(_,x) -> newgen x
    | OVarDummy as v -> v

(** Type variable. *)
type tVar = 
    TVar of string
  | TVarDummy							      (* temporary place holder in applications [f a] *)

(** Universe variable. *)
type uVar = UVar of string

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
    The type [uLevel] implements all aspects of judging that we have a valid
    uLevel, except for possibly constraining the list of variables used to members
    of a given list.
 *)
type uLevel =
  | Unumeral of int
	(** A u-level [n] stages above the bottom-most universe. *)
  | Uvariable of uVar
	(** A u-level variable. *)
  | Uplus of uLevel * int
	(** A pair [(M,n)], denoting [M+n], the n-th successor of [M].  Here [n] should be nonnegative *)
  | Umax of uLevel * uLevel
	(** A pair [(M,M')] denoting [max(M,M')]. *)

type  oBinding = oVar * oExpr
and   tBinding = oVar * tExpr
and   tBinding2= oVar * oVar  * tExpr
and  toBinding = oVar * tExpr * oBinding
and  ooBinding = oVar * oExpr * oBinding
and ttoBinding = oVar * tExpr * toBinding
and oooBinding = oVar * oExpr * ooBinding

(** [tExpr] is the type of T-expressions. *)
and tExpr =
  (* TS0 *)
  | Tvariable of tVar
  | El of oExpr
	(** [El]; converts an object term into the corresponding type term *)
  | T_U of uLevel
	(** [T_U m]; a u-level expression, as a type *)
  | Pi of tExpr * tBinding
	(** [Pi(T,(x,T')) <--> \[Pi;x\](T,T')] *)
    (* TS1 *)
  | Sigma of tExpr * tBinding
	(** [Sigma(T,(x,T')) <--> \[Sigma;x\](T,T')] *)
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
	  Perhaps he intended to write [\[El\](\[empty\]())] for it. *)
      (* TS5 *)
  | T_IC of tExpr * oExpr * ttoBinding
	(** [T_IC(A,a,(x,B,(y,D,(z,q)))) <--> \[IC;x,y,z\](A,a,B,D,q)]
	 *)
      (* TS6 *)
  | Id of tExpr * oExpr * oExpr
      (** Identity type; paths type. *)
      (* TS7 *)
      
(** [oExpr] is the type of o-expressions. *)
and oExpr =
    (* TS0 *)
  | Ovariable of oVar
	(** An o-variable. *)
  | O_u of uLevel
	(** [u]; universe as an object. *)
  | O_j of uLevel * uLevel
	(** [j](U,U') *)
  | O_ev of oExpr * oExpr * tBinding
	(** [O_ev(f,o,(x,T)) <--> \[ev;x\](f,o,T)]
	    
	    Application of the function [f] to the argument [o].
	    
	    Here [T], with the type of [o] replacing [x], gives the type of the result.

	    By definition, such subexpressions [T] are not essential.
	 *)
  | O_lambda of tExpr * oBinding
	(** [O_lambda(T,(x,o)) <--> \[lambda;x\](T,o)] *)
  | O_forall of uLevel * uLevel * oExpr * oBinding
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
  | O_total of uLevel * uLevel * oExpr * oBinding
	(** [O_total(m1,m2,o1,(x,o2)) <--> \[total;x\](m1,m2,o1,o2)]

	    Corresponds to [total] or [prod] in the paper. *)
	(* TS2 *)
  | O_pt
      (** Corresponds to [\[pt\]] in the paper. *)
      
  | O_pt_r of oExpr * tBinding
	(** [O_pt_r(o,(x,T)) <--> \[pt_r;x\](o,T)]
	    
	    [O_pt_r] is the eliminator for [T_Pt]. *)
  | O_tt
      (** [O_tt <--> \[tt\]()]
	  
	  [O_tt] is the unique instance of the unit type [T_Pt]. *)
      (* TS3 *)
  | O_coprod of uLevel * uLevel * oExpr * oExpr
	(** The type of the term is given by the [max] of the two u-levels. *)
  | O_ii1 of tExpr * tExpr * oExpr
	(** The type of a term [O_ii1(T,T',o)] is [T_Coprod(T,T')]; here [o] has type [T] *)
  | O_ii2 of tExpr * tExpr * oExpr
	(** The type of a term [O_ii2(T,T',o)] is [T_Coprod(T,T')]; here [o] has type [T'] *)
  | Sum of tExpr * tExpr * oExpr * oExpr * oExpr * tBinding
	(** The type of a term [Sum(T,T',s,s',o,(x,S))] is [S], with [x] replaced by [o]. *)
	(* TS4 *)
  | O_empty
      (** [ O_empty <--> \[empty\]() ]
				    
	  The type of [\[empty\]] is the smallest universe, [Unumeral 0]. 

	  Remember to make [El]([empty]()) reduce to [Empty]().
       *)
  | O_empty_r of tExpr * oExpr
	(** The elimnination rule for the empty type.

	    The type of [O_empty_r(T,o)] is [T].  Here the type of [o] is [T_Empty], the empty type. *)
  | O_c of tExpr * oExpr * ttoBinding * oExpr * oExpr
	(** [O_c(A,a,(x,B,(y,D,(z,q))),b,f) <--> \[c;x,y,z\](A,a,B,D,q,b,f)]
	    
	    Corresponds to [c] in the paper. *)
  | O_ic_r of tExpr * oExpr * ttoBinding * oExpr * tBinding2 * oExpr
	(** [O_ic_r(A,a,(x,B,(y,D,(z,q))),i,(x',v,S),t) <--> \[ic_r;x,y,z,x',v\](A,a,B,D,q,i,S,t)]
	    
	    ic_r is the elimination rule for inductive types (generalized W-types) *)
  | O_ic of uLevel * uLevel * uLevel * oExpr * oExpr * oooBinding
	(** [O_ic(M1,M2,M3,oA,a,(x,oB,(y,oD,(z,q)))) <--> \[[ic;x,y,z](M1,M2,M3,oA,a,oB,oD,q)\]]
	    
	    Corresponds to [ic].  Its type is the max of the three u-level expressions. *)
	(* TS6 *)
  | O_paths of uLevel * oExpr * oExpr * oExpr
	(** The object corresponding to the identity type [Id].  

	    Its type is the type corresponding to the given universe level. *)
  | O_refl of tExpr * oExpr
	(** Reflexivity, or the constant path. 
	    
	    The type of [O_refl(T,o)] is [Id(T,o,o)]. *)
  | O_J of tExpr * oExpr * oExpr * oExpr * oExpr * tBinding2
	(** The elimination rule for Id; Id-elim.

	    The type of [O_J(T,a,b,q,i,(x,e,S))] is [S\[b/x,i/e\]]. *)
      (* TS7 *)
  | O_rr0 of uLevel * uLevel * oExpr * oExpr * oExpr
	(** Resizing rule.

	    The type of [O_rr0(M_2,M_1,s,t,e)] is [T_U(M_1)], resized downward from [T_U M_2].

	    By definition, the subexpressions [t] and [e] are not essential.
	 *)
  | O_rr1 of uLevel * oExpr * oExpr
	(** Resizing rule.

	    The type of [O_rr1(M,a,p)] is [T_U(Unumeral 0)], resized downward from [T_U M].

	    By definition, the subexpression [p] is not essential.
	 *)


(** 
    A universe context [UC = (Fu,A)] is represented a list of universe variables [Fu] and a list of
    equations [M_i = N_i] between two u-level expressions formed from the variables in [Fu]
    that defines the admissible subset [A] of the functions [Fu -> nat].  It's just the subset
    that matters.
 *) 
type uContext = UContext of uVar list * (uLevel * uLevel) list
let emptyUContext = UContext ([],[])

(** t-context; a list of t-variables declared as "Type". *)
type tContext = tVar list
let emptyTContext : tContext = []

(** o-context; a list of o-variables with T-expressions representing their declared type. *)
type oContext = (oVar * tExpr) list
let emptyOContext : oContext = []

type context = Context of uContext * tContext * oContext			      (* [Gamma] *)
let emptyContext : context = Context (emptyUContext,emptyTContext,emptyOContext)
      
type judgementBody =
  | EmptyJ
	(** Gamma |> *)
  | TypeJ of oExpr * tExpr
	(** Gamma |- o : T *)
  | TypeEqJ of tExpr * tExpr
	(** Gamma |- T = T' *)
  | ObjEqJ of oExpr * oExpr * tExpr
	(** Gamma |- o = o' : T *)
let emptyJudgementBody = EmptyJ
type judgement = context * judgementBody
let emptyJudgment : judgement = (emptyContext,emptyJudgementBody)
type ruleCitation = Rule of int
type derivation = 
  | Derivation of derivation list * ruleCitation * judgement
type ruleLabel = int
type ruleParm =
  | RPNone
  | RPot of oVar * tVar
  | RPo of oVar
let rec getType (o:oVar) = function
    (o',t) :: _ when o = o' -> t
  | _ :: gamma -> getType o gamma
  | [] -> raise VariableNotInContext
let inferenceRule : ruleLabel * ruleParm * derivation list -> derivation = function
    (1,RPNone,[]) -> Derivation([],Rule 1,emptyJudgment)
  | (2,RPot (o,t),([Derivation(_,_,(Context (uc,tc,oc),EmptyJ))] as derivs)) -> Derivation(derivs,Rule 2,(Context (uc,tc,(o,Tvariable t) :: oc),EmptyJ))
  | (3,RPo o,([Derivation(_,_,(Context (_,_,oc) as gamma, _))] as derivs)) -> Derivation(derivs,Rule 3,(gamma,TypeJ(Ovariable o,getType o oc)))
  | _ -> raise NoMatchingRule
let d1 = inferenceRule(1,RPNone,[])
let d2 = inferenceRule(2,RPot (OVar "x", TVar "X"), [d1])
let d3 = inferenceRule(3,RPo (OVar "x"), [d2])

(* Abbreviations, conventions, and definitions; from the paper *)

type identifier = Ident of string
type definition = 
  | TDefinition of identifier * context         * tExpr
  | ODefinition of identifier * context * oExpr * tExpr

(*
 For emacs:
 Local Variables:
  coding: latin-1
  compile-command: "make run "
  comment-column: 70
 End:
*)
