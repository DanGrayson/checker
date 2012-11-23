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
  | VarEmptyHole
let make_Var c = Var c
let vartostring' = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | VarEmptyHole -> "_"
  | VarUnused -> "_"
let vartostring v = vartostring' (strip_pos_var v)
type vartype = Ulevel_variable | Type_variable | Object_variable

(** A u-level expression, [M], is constructed inductively as: [n], [v], [M+n], or
    [max(M,M')], where [v] is a universe variable and [n] is a natural number.
 *)

(** The various labels for u-expressions of TS. *)
type uHead =
  | Uplus of int
	(** A pair [(M,n)], denoting [M+n], the n-th successor of [M].  Here [n] should be nonnegative *)
  | Umax
	(** A pair [(M,M')] denoting [max(M,M')]. *)
  | UEmptyHole
        (** A u-level, to be filled in later, by type checking. *)
  | UNumberedEmptyHole of int
        (** A u-level, to be filled in later, by type checking. *)
  | U_def_app of string

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
  | OO_numberedEmptyHole of int
        (** A hole to be filled in later, by type checking. *)
  | OO_def_app of string

type label =
  | UU of uHead
  | TT of tHead
  | OO of oHead
	
type expr = 
  | POS of position * bare_expr
	(** a wrapper that gives the position in the source code, for error messages *)
  | LAMBDA of var * expr list
	(** LAMBDA is the lambda of LF.
	    
	    The variable is bound in each of the expressions of the list, and
	    the lambda expression is to be thought of as returning a tuple, with one
	    member for each expression in the list.

	    Notice that we can't wrap a LAMBDA expression inside a position.  We do
	    that to make OCAML pattern matching feasible.*)
and bare_expr =
  | Variable of var'
	(** A variable. *)
  | APPLY of label * expr list
	(** APPLY is function application in LF *)

let uhead_to_string = function
  | Uplus n -> "uplus;" ^ (string_of_int n)
  | Umax -> "max"
  | UEmptyHole -> "_"
  | UNumberedEmptyHole n -> "_" ^ (string_of_int n)
  | U_def_app d -> "udef;" ^ d
let thead_to_string = function
  | TT_EmptyHole -> "__"
  | TT_NumberedEmptyHole n -> "__" ^ (string_of_int n)
  | TT_El -> "El"
  | TT_U -> "U"
  | TT_Pi -> "Pi"
  | TT_Sigma -> "Sigma"
  | TT_Pt -> "Pt"
  | TT_Coprod -> "Coprod"
  | TT_Coprod2 -> "Coprod2"
  | TT_Empty -> "Empty"
  | TT_IC -> "IC"
  | TT_Id -> "Id"
  | TT_def_app d -> "tdef;" ^ d
let ohead_to_string = function
  | OO_emptyHole -> "_"
  | OO_numberedEmptyHole n -> "_" ^ (string_of_int n)
  | OO_u -> "u"
  | OO_j -> "j"
  | OO_ev -> "ev"
  | OO_lambda -> "lambda"
  | OO_forall -> "forall"
  | OO_def_app d -> "odef;" ^ d
  | OO_pair -> "pair"
  | OO_pr1 -> "pr1"
  | OO_pr2 -> "pr2"
  | OO_total -> "total"
  | OO_pt -> "pt"
  | OO_pt_r -> "pt_r"
  | OO_tt -> "tt"
  | OO_coprod -> "coprod"
  | OO_ii1 -> "ii1"
  | OO_ii2 -> "ii2"
  | OO_sum -> "sum"
  | OO_empty -> "empty"
  | OO_empty_r -> "empty_r"
  | OO_c -> "c"
  | OO_ic_r -> "ic_r"
  | OO_ic -> "ic"
  | OO_paths -> "paths"
  | OO_refl -> "refl"
  | OO_J -> "J"
  | OO_rr0 -> "rr0"
  | OO_rr1 -> "rr1"
let head_to_string = function
  | UU h -> "[" ^ uhead_to_string h ^ "]"
  | TT h -> "[" ^ thead_to_string h ^ "]"
  | OO h -> "[" ^ ohead_to_string h ^ "]"

let rec get_u = function
  | POS (_,APPLY(UU _,u)) -> u
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

let rec isU = 
  let isU' = function
    | Variable _ -> true		(* not right, should look in the context *)
    | APPLY(UU _, _) -> true
    | _ -> false
  in function
    | POS(_,x) -> isU' x
    | LAMBDA(x,bodies) -> raise Error.Internal
let chku u = if not (isU u) then raise Error.Internal; u
let chkulist us = List.iter (fun u -> let _ = chku u in ()) us; us

let rec isT = 
  let isT' = function
    | Variable _ -> true		(* not right, should look in the context *)
    | APPLY(TT _, _) -> true
    | _ -> false
  in function
    | POS(_,x) -> isT' x
    | LAMBDA(x,bodies) -> raise Error.Internal
let chkt t = if not (isT t) then raise Error.Internal; t
let chktlist ts = List.iter (fun t -> let _ = chkt t in ()) ts; ts

let rec isO = 
  let isO' = function
    | Variable _ -> true		(* not right, should look in the context *)
    | APPLY(OO _, _) -> true
    | _ -> false
  in function
    | POS(_,x) -> isO' x
    | LAMBDA(x,bodies) -> raise Error.Internal

let chko o = if not (isO o) then raise Error.Internal; o
let chkolist os = List.iter (fun o -> let _ = chko o in ()) os; os

type expr_descriptor =
  | U_spot
  | T_spot
  | O_spot
  | B_spot of expr_descriptor list

let template = function
  | LAMBDA(x,bodies) -> ()
  | POS(pos,e) -> match e with
    | Variable t -> ()
    | APPLY(h,args) -> (
	match h with
	| UU uh -> (
	    match uh with 
	    | Uplus n -> ()
	    | Umax -> ()
	    | UEmptyHole -> ()
	    | UNumberedEmptyHole n -> ()
	    | U_def_app d -> ()
	   )
	| TT th -> (
	    match th with 
	    | TT_EmptyHole -> ()
	    | TT_NumberedEmptyHole n -> ()
	    | TT_El -> ()
	    | TT_U -> ()
	    | TT_Pi -> (
		match args with
		| [t1; LAMBDA( x, [t2] )] -> ()
		| _ -> raise Error.Internal)
	    | TT_Sigma -> (
		match args with
		| [t1; LAMBDA( x, [t2] )] -> ()
		| _ -> raise Error.Internal)
	    | TT_Pt -> ()
	    | TT_Coprod -> ()
	    | TT_Coprod2 -> (
		match args with
		| [t;t'; LAMBDA( x,[u]);LAMBDA( x', [u']);o] -> ()
		| _ -> raise Error.Internal)
	    | TT_Empty -> ()
	    | TT_IC -> (
		match args with
		| [tA; a; LAMBDA( x, [tB;LAMBDA( y, [tD;LAMBDA( z, [q])])])] -> ()
		| _ -> raise Error.Internal)
	    | TT_Id -> (
		match args with
		| [tX; x; x'] -> ()
		| _ -> raise Error.Internal)
	    | TT_def_app d -> ()
	   )
	| OO oh -> (
	    match oh with
	    | OO_emptyHole -> ()
	    | OO_numberedEmptyHole n -> ()
	    | OO_u -> ()
	    | OO_j -> ()
	    | OO_ev -> (
		match args with
		| [f;o;LAMBDA( x,[t])] -> ()
		| [f;o] -> ()
		| _ -> raise Error.Internal)
	    | OO_lambda -> (
		match args with
		| [t;LAMBDA( x,[o])] -> ()
		| _ -> raise Error.Internal)
	    | OO_forall -> (
		match args with
		| [u;u';o;LAMBDA( x,[o'])] -> ()
		| _ -> raise Error.Internal)
	    | OO_def_app d -> ()
	    | OO_pair -> ()
	    | OO_pr1 -> ()
	    | OO_pr2 -> ()
	    | OO_total -> ()
	    | OO_pt -> ()
	    | OO_pt_r -> ()
	    | OO_tt -> ()
	    | OO_coprod -> ()
	    | OO_ii1 -> ()
	    | OO_ii2 -> ()
	    | OO_sum -> ()
	    | OO_empty -> ()
	    | OO_empty_r -> ()
	    | OO_c -> ()
	    | OO_ic_r -> ()
	    | OO_ic -> ()
	    | OO_paths -> ()
	    | OO_refl -> ()
	    | OO_J -> ()
	    | OO_rr0 -> ()
	    | OO_rr1 -> ()
	   )
       )

let make_UU h a = APPLY(UU h, a)
let make_TT h a = APPLY(TT h, a)
let make_OO h a = APPLY(OO h, a)
let make_Variable x = Variable x

let make_BB1 v x = LAMBDA( v, [x])
let make_BB2 v x y = LAMBDA( v, [x;y])

let make_TT_EmptyHole = make_TT TT_Empty []
let make_TT_NumberedEmptyHole n = make_TT (TT_NumberedEmptyHole n) []
let make_TT_El x = make_TT TT_El [chko x]
let make_TT_U x = make_TT TT_U [chku x]
let make_TT_Pi    t1 (x,t2) = make_TT TT_Pi    [chkt t1; make_BB1 x (chkt t2)]
let make_TT_Sigma t1 (x,t2) = make_TT TT_Sigma [chkt t1; make_BB1 x (chkt t2)]
let make_TT_Pt = make_TT TT_Pt []
let make_TT_Coprod t t' = make_TT TT_Coprod [chkt t;chkt t']
let make_TT_Coprod2 t t' (x,u) (x',u') o = make_TT TT_Coprod2 [chkt t; chkt t'; make_BB1 x (chkt u); make_BB1 x' (chkt u'); chko o]
let make_TT_Empty = make_TT TT_Empty []
let make_TT_IC tA a (x,tB,(y,tD,(z,q))) =
  make_TT TT_IC [chkt tA; chko a; make_BB2 x (chkt tB) (make_BB2 y (chkt tD) (make_BB1 z (chko q)))]
let make_TT_Id t x y = make_TT TT_Id [chkt t;chko x;chko y]
let make_TT_def_app name u t o = make_TT (TT_def_app name) (List.flatten [chkulist u;chktlist t;chkolist o])

let make_OO_emptyHole = make_OO OO_emptyHole []
let make_OO_numberedEmptyHole n = make_OO (OO_numberedEmptyHole n) []
let make_OO_u m = make_OO OO_u [chku m]
let make_OO_j m n = make_OO OO_j [chku m; chku n]
let make_OO_ev f p (v,t) = make_OO OO_ev [chko f;chko p;make_BB1 v (chkt t)]
let make_OO_ev_hole f p = make_OO OO_ev [chko f;chko p] (* fill in third argument later *)
let make_OO_lambda t (v,p) = make_OO OO_lambda [chkt t; make_BB1 v (chko p)]
let make_OO_forall m m' n (v,o') = make_OO OO_forall [chku m;chku m';chko n;make_BB1 v (chko o')]
let make_OO_pair a b (x,t) = make_OO OO_pair [chko a;chko b;make_BB1 x (chkt t)]
let make_OO_pr1 t (x,t') o = make_OO OO_pr1 [chkt t;make_BB1 x (chkt t'); chko o]
let make_OO_pr2 t (x,t') o = make_OO OO_pr2 [chkt t;make_BB1 x (chkt t'); chko o]
let make_OO_total m1 m2 o1 (x,o2) = make_OO OO_total [chku m1;chku m2;chko o1;make_BB1 x (chko o2)]
let make_OO_pt = make_OO OO_pt []
let make_OO_pt_r o (x,t) = make_OO OO_pt_r [chko o;make_BB1 x (chkt t)]
let make_OO_tt = make_OO OO_tt []
let make_OO_coprod m1 m2 o1 o2 = make_OO OO_coprod [chku m1; chku m2; chko o1; chko o2]
let make_OO_ii1 t t' o = make_OO OO_ii1 [chkt t;chkt t';chko o]
let make_OO_ii2 t t' o = make_OO OO_ii2 [chkt t;chkt t';chko o]
let make_OO_sum tT tT' s s' o (x,tS) = make_OO OO_sum [chkt tT; chkt tT'; chko s; chko s'; chko o; make_BB1 x (chkt tS)]
let make_OO_empty = make_OO OO_empty []
let make_OO_empty_r t o = make_OO OO_empty_r [chkt t; chko o]
let make_OO_c tA a (x,tB,(y,tD,(z,q))) b f = make_OO OO_c [
  chko a; 
  make_BB2 x
    (chkt tB)
    (make_BB2 y
       (chkt tD)
       (make_BB1 z
	  (chko q))) ]
let make_OO_ic_r tA a (x,tB,(y,tD,(z,q))) i (x',(v,tS)) t = make_OO OO_ic_r [
  chkt tA; chko a;
  make_BB2 x
    (chkt tB) 
    (make_BB2 y
       (chkt tD)
       (make_BB1 z
	  (chko q)));
  chko i; 
  make_BB1  x'
    (make_BB1 v
       (chkt tS)); 
  chko t]
let make_OO_ic m1 m2 m3 oA a (x,oB,(y,oD,(z,q))) = make_OO OO_ic [
  chku m1; chku m2; chku m3;
  chko oA; chko a;
  make_BB2 x
    (chko oB)
    (make_BB2 y
       (chko oD)
       (make_BB1 z
	  (chko q))) ]
let make_OO_paths m t x y = make_OO OO_paths [chku m; chkt t; chko x; chko y]
let make_OO_refl t o = make_OO OO_refl [chkt t; chko o]
let make_OO_J tT a b q i (x,(e,tS)) = make_OO OO_J [chkt tT; chko a; chko b; chko q; chko i; make_BB1 x (make_BB1 e (chkt tS))]
let make_OO_rr0 m2 m1 s t e = make_OO OO_rr0 [chku m2; chku m1; chko s; chko t; chko e]
let make_OO_rr1 m a p = make_OO OO_rr1 [chku m; chko a; chko p]
let make_OO_def_app name u t c = make_OO (OO_def_app name) (List.flatten [chkulist u; chktlist t; chkolist c])

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


(* obsolete

type var = U of var' | T of var' | O of var'

*)

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
  | VarEmptyHole -> env

let obind (v,t) env = obind' (strip_pos_var v, t) env

(*
  Local Variables:
  compile-command: "ocamlbuild typesystem.cmo "
  End:
 *)
