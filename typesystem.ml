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

(** Universe variable. *)
type uVar = position * uVar'
and uVar' = UVar of string
let make_uVar c = UVar c

(** Type variable. *)
type tVar = position * tVar'
and tVar' = TVar of string
let make_tVar c = TVar c

(** Object variable. *)
type oVar = position * oVar'
and oVar' =
    OVar of string
  | OVarGen of int * string
  | OVarUnused
  | OVarEmptyHole
let make_oVar c = OVar c

let strip_pos_var : position * 'a -> 'a = snd
let get_pos_var : position * 'a -> position = fst

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
    The type [uExpr] implements all aspects of judging that we have a valid
    uExpr, except for possibly constraining the list of variables used to members
    of a given list.
 *)
type uExpr =
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
	
type expr = 
  | Expr of label * expr list
  | UU of uExpr
	(** A u-level expression. *)
  | TT_variable of tVar'
	(** A t-variable. *)
  | OO_variable of oVar'
	(** An o-variable. *)
  | POS of position * expr
	(** a wrapper that gives the position in the source code, for error messages *)
and tExpr = expr			(*temporary*)
and oExpr = expr			(*temporary*)
and label =
  | OO_binder of oVar
	(** the variable is bound in each of the expressions of the list above *)
  | TT of tHead
  | OO of oHead
and tHead =
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
      (* TS4 *)
  | TT_Empty
      (** The empty type.  
	  
	  Voevodsky doesn't list this explicitly in the definition of TS4, but it gets used in derivation rules, so I added it.
	  Perhaps he intended to write [\[T_El\](\[empty\]())] for it. *)
      (* TS5 *)
  | TT_IC
	(** [T_IC(A,a,(x,B,(y,D,(z,q)))) <--> \[IC;x,y,z\](A,a,B,D,q)]
	 *)
      (* TS6 *)
  | TT_Id
      (** Identity type; paths type. *)
      (* TS7: *)
      (* end of TS *)
  | TT_EmptyHole
      (** a hole to be filled in later  *)
  | TT_NumberedEmptyHole of int
        (** A hole to be filled in later, by type checking. *)
  | TT_def_app of string
  | TT_nat
      (** nat 

	  The type of natural numbers. *)
and oHead =
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
	(* TS2 *)
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
	(** [O_c(A,a,(x,B,(y,D,(z,q))),b,f) <--> \[c;x,y,z\](A,a,B,D,q,b,f)]
	    
	    Corresponds to [c] in the paper. *)
  | OO_ic_r
	(** [O_ic_r(A,a,(x,B,(y,D,(z,q))),i,(x',v,S),t) <--> \[ic_r;x,y,z,x',v\](A,a,B,D,q,i,S,t)]
	    
	    ic_r is the elimination rule for inductive types (generalized W-types) *)
  | OO_ic
	(** [O_ic(M1,M2,M3,oA,a,(x,oB,(y,oD,(z,q)))) <--> \[[ic;x,y,z](M1,M2,M3,oA,a,oB,oD,q)\]]
	    
	    Corresponds to [ic].  Its type is the max of the three u-level expressions. *)
	(* TS6 *)
  | OO_paths
	(** The object corresponding to the identity type [Id].  

	    Its type is the type corresponding to the given universe level. *)
  | OO_refl
	(** Reflexivity, or the constant path. 
	    
	    The type of [O_refl(T,o)] is [Id(T,o,o)]. *)
  | OO_J
	(** The elimination rule for Id; Id-elim.

	    The type of [O_J(T,a,b,q,i,(x,e,S))] is [S\[b/x,i/e\]]. *)
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
  | OO_emptyHole
      (** a hole to be filled in later *)
  | OO_numeral of int
        (** A numeral.
	    
	    We add this variant temporarily to experiment with parsing
	    conflicts, when numerals such as 4, can be considered either as
	    o-expressions (S(S(S(S O)))) or as universe levels.  *)
  | OO_numberedEmptyHole of int
        (** A hole to be filled in later, by type checking. *)
  | OO_def_app of string

let with_pos pos u = POS (pos, u)
let rec strip_pos = function
| POS(_,x) -> strip_pos x
| e -> e
let get_pos = function
| POS(pos,_) -> pos
| _ -> raise InternalError
let nowhere x = with_pos Nowhere x

let rec isU = function
| POS(_,x) -> isU x
| UU _ -> true
| _ -> false
let chku u = if not (isU u) then raise InternalError; u
let chkulist us = List.iter (fun u -> let _ = chku u in ()) us; us

let rec isT = function
| POS(_,x) -> isT x
| TT_variable _ -> true
| Expr(TT _, _) -> true
| _ -> false
let chkt t = if not (isT t) then raise InternalError; t
let chktlist ts = List.iter (fun t -> let _ = chkt t in ()) ts; ts

let rec isO = function
| POS(_,x) -> isO x
| OO_variable _ -> true
| Expr(OO _, _) -> true
| _ -> false
let chko o = if not (isO o) then raise InternalError; o
let chkolist os = List.iter (fun o -> let _ = chko o in ()) os; os

let make_UU u = UU u
let make_TT h a = Expr(TT h, a)
let make_OO h a = Expr(OO h, a)
let make_TT_variable x = TT_variable x
let make_OO_variable v = OO_variable v

let make_OO_binder1 v x = Expr(OO_binder v, [x])
let make_OO_binder2 v x y = Expr(OO_binder v, [x;y])

let make_TT_EmptyHole = make_TT TT_Empty []
let make_TT_NumberedEmptyHole n = make_TT (TT_NumberedEmptyHole n) []
let make_TT_El x = make_TT TT_El [chko x]
let make_TT_U x = make_TT TT_U [chku x]
let make_TT_Pi    t1 (x,t2) = make_TT TT_Pi    [chkt t1; make_OO_binder1 x (chkt t2)]
let make_TT_Sigma t1 (x,t2) = make_TT TT_Sigma [chkt t1; make_OO_binder1 x (chkt t2)]
let make_TT_Pt = make_TT TT_Pt []
let make_TT_Coprod t t' = make_TT TT_Coprod [chkt t;chkt t']
let make_TT_Coprod2 t t' (x,u) (x',u') o = make_TT TT_Coprod2 [chkt t; chkt t'; make_OO_binder1 x (chkt u); make_OO_binder1 x' (chkt u'); chko o]
let make_TT_Empty = make_TT TT_Empty []
let make_TT_IC tA a (x,tB,(y,tD,(z,q))) =
  make_TT TT_IC [chkt tA; chko a; make_OO_binder2 x (chkt tB) (make_OO_binder2 y (chkt tD) (make_OO_binder1 z (chko q)))]
let make_TT_Id t x y = make_TT TT_Id [chkt t;chko x;chko y]
let make_TT_def_app name u t o = make_TT (TT_def_app name) (List.flatten [chkulist u;chktlist t;chkolist o])
let make_TT_nat = make_TT TT_nat []

let make_OO_emptyHole = make_OO OO_emptyHole []
let make_OO_numberedEmptyHole n = make_OO (OO_numberedEmptyHole n) []
let make_OO_numeral n = make_OO (OO_numeral n) []
let make_OO_u m = make_OO OO_u [chku m]
let make_OO_j m n = make_OO OO_j [chku m; chku n]
let make_OO_ev f p (v,t) = make_OO OO_ev [chko f;chko p;make_OO_binder1 v (chkt t)]
let make_OO_ev_hole f p = make_OO OO_ev [chko f;chko p] (* fill in third argument later *)
let make_OO_lambda t (v,p) = make_OO OO_lambda [chkt t; make_OO_binder1 v (chko p)]
let make_OO_forall m m' o (v,o') = make_OO OO_forall [chku m;chku m';chko o;make_OO_binder1 v (chko o')]
let make_OO_pair a b (x,t) = make_OO OO_pair [chko a;chko b;make_OO_binder1 x (chkt t)]
let make_OO_pr1 t (x,t') o = make_OO OO_pr1 [chkt t;make_OO_binder1 x (chkt t'); chko o]
let make_OO_pr2 t (x,t') o = make_OO OO_pr2 [chkt t;make_OO_binder1 x (chkt t'); chko o]
let make_OO_total m1 m2 o1 (x,o2) = make_OO OO_total [chku m1;chku m2;chko o1;make_OO_binder1 x (chko o2)]
let make_OO_pt = make_OO OO_pt []
let make_OO_pt_r o (x,t) = make_OO OO_pt_r [chko o;make_OO_binder1 x (chkt t)]
let make_OO_tt = make_OO OO_tt []
let make_OO_coprod m1 m2 o1 o2 = make_OO OO_coprod [chku m1; chku m2; chko o1; chko o2]
let make_OO_ii1 t t' o = make_OO OO_ii1 [chkt t;chkt t';chko o]
let make_OO_ii2 t t' o = make_OO OO_ii2 [chkt t;chkt t';chko o]
let make_OO_sum tT tT' s s' o (x,tS) = make_OO OO_sum [chkt tT; chkt tT'; chko s; chko s'; chko o; make_OO_binder1 x (chkt tS)]
let make_OO_empty = make_OO OO_empty []
let make_OO_empty_r t o = make_OO OO_empty_r [chkt t; chko o]
let make_OO_c tA a (x,tB,(y,tD,(z,q))) b f = make_OO OO_c [
  chko a; 
  make_OO_binder2 
    x
    (chkt tB)
    (make_OO_binder2 
       y
       (chkt tD)
       (make_OO_binder1 z (chko q))) ]
let make_OO_ic_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_OO OO_ic_r [
  chkt tA; chko a;
  make_OO_binder2 x (chkt tB) (make_OO_binder2 y (chkt tD) (make_OO_binder1 z (chko q)));
  chko i; make_OO_binder1  x' (make_OO_binder1 v (chkt tS)); 
  chko t]
let make_OO_ic m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_OO OO_ic [
  chku m1; chku m2; chku m3;
  chko oA; chko a;
  make_OO_binder2 x (chko oB) (make_OO_binder2 y (chko oD) (make_OO_binder1 z (chko q)))]
let make_OO_paths m t x y = make_OO OO_paths [chku m; chkt t; chko x; chko y]
let make_OO_refl t o = make_OO OO_refl [chkt t; chko o]
let make_OO_J tT a b q i (x,(e,tS)) = make_OO OO_J [chkt tT; chko a; chko b; chko q; chko i; make_OO_binder1 x (make_OO_binder1 e (chkt tS))]
let make_OO_rr0 m2 m1 s t e = make_OO OO_rr0 [chku m2; chku m1; chko s; chko t; chko e]
let make_OO_rr1 m a p = make_OO OO_rr1 [chku m; chko a; chko p]
let make_OO_def_app name u t c = make_OO (OO_def_app name) (List.flatten [chkulist u; chktlist t; chkolist c])

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


(*
  Local Variables:
  compile-command: "ocamlbuild typesystem.cmo "
  End:
 *)
