open Typesystem
open Tau
open Equality

let rec uexprcheck pos env = 
  let rec ucheckexpr' env = function
    | Upos (pos,u) -> uexprcheck pos env u
    | Uvariable UVar s -> (
	match (
	  try List.assoc s env.lookup_order
	  with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound u-variable: "^s)))
	with 
	  U _ -> ()
	| T _ -> raise (Error.TypeCheckingFailure (pos, "expected a u-variable but found a t-variable: "^s))
	| O _ -> raise (Error.TypeCheckingFailure (pos, "expected a u-variable but found an o-variable: "^s)))
    | Uplus (u,n) -> ucheckexpr' env u
    | Umax (u,v) -> ucheckexpr' env u; ucheckexpr' env v
    | U_def _ -> raise Error.NotImplemented
    | UEmptyHole | UNumberedEmptyHole _ -> raise (Error.TypeCheckingFailure(pos, "empty hole for u-expression found"))
  in ucheckexpr' env

let rec ucheck pos env =
  let rec ucheck' env = function
    | POS(pos,e) -> ucheck pos env e
    | UU u -> uexprcheck pos env u
    | _ -> raise Error.Internal
  in ucheck' env

let rec tcheck pos env = 
  let rec tcheck' env = function
    | POS(pos,e) -> tcheck pos env e
    | UU u -> uexprcheck pos env u
    | TT_variable TVar s -> (
	match (
	  try List.assoc s env.lookup_order
	  with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound t-variable: "^s)))
	with 
	  U _ -> raise (Error.TypeCheckingFailure (pos, "expected a t-variable but found a u-variable: "^s))
	| T _ -> ()
	| O _ -> raise (Error.TypeCheckingFailure (pos, "expected a t-variable but found an o-variable: "^s)))
    | OO_variable o -> raise Error.Internal
    | Expr(h,args) -> (
	match h with
	| BB x -> raise Error.Internal
	| TT th -> (
	    match th with 
	    | TT_EmptyHole | TT_NumberedEmptyHole _ -> raise (Error.TypeCheckingFailure(pos,"empty hole for t-expression found"))
	    | TT_El -> ocheckn 1 pos env args
	    | TT_U -> ucheckn 1 pos env args
	    | TT_Sigma | TT_Pi -> (
		match args with
		| [t1; Expr( BB x, [t2] )] -> tcheck' env t1; tcheck_binder pos env x t1 t2
		| _ -> raise Error.Internal)
	    | TT_Pt -> ()
	    | TT_Coprod -> (
		match args with
		| [t1; t2] -> tcheck' env t1; tcheck' env t2
		| _ -> raise Error.Internal)
	    | TT_Coprod2 -> (
		match args with 
		| [t;t'; Expr(BB x,[u]);Expr(BB x', [u']);o] -> raise Error.NotImplemented
		| _ -> raise Error.Internal)
	    | TT_Empty -> ()
	    | TT_IC -> (
		match args with [tA; a; Expr(BB x, [tB;Expr( BB y, [tD;Expr( BB z, [q])])])] -> raise Error.NotImplemented
		| _ -> raise Error.Internal)
	    | TT_Id -> (
	      match args with
	      | [t; x; y] -> (
		  tcheck' env t; ocheck pos env x; ocheck pos env y; 
		  overify pos env x t; overify pos env y t)
	      | _ -> raise Error.Internal)
	    | TT_def_app d -> raise Error.NotImplemented
	    | TT_nat -> ()
	   )
	| OO _ -> raise (Error.TypeCheckingFailure(pos, "expected a t-expression but found an o-expression"))
       )
  in tcheck' env
and ocheck pos env = function
  | POS(pos,e) -> ocheck pos env e
  | UU u -> uexprcheck pos env u
  | TT_variable t -> ()
  | OO_variable OVarGen (i,s) -> raise Error.NotImplemented
  | OO_variable OVarUnused -> raise Error.Internal
  | OO_variable OVarEmptyHole -> raise Error.Internal
  | OO_variable OVar s -> (
      match
	try List.assoc s env.lookup_order
	with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound o-variable: "^s))
      with 
	U _ -> raise (Error.TypeCheckingFailure (pos, "expected an o-variable but found a u-variable: "^s))
      | T _ -> raise (Error.TypeCheckingFailure (pos, "expected an o-variable but found a t-variable: "^s))
      | O _ -> ())
  | Expr(h,args) -> (
      match h with
      | BB x -> raise Error.Internal	(* should have been handled higher up *)
      | TT th -> raise (Error.TypeCheckingFailure(pos, "expected an o-expression but found a t-expression"))
      | OO oh -> (
	  match oh with
	  | OO_emptyHole | OO_numberedEmptyHole _ -> raise Error.Internal
	  | OO_u -> ucheckn 1 pos env args
	  | OO_j -> ucheckn 2 pos env args
	  | OO_ev -> (
	      match args with 
	      | [f;o] -> raise Error.Internal (* type should have been filled in by now *)
	      | [f;x;Expr(BB v,[t])] -> (
		  ocheck pos env f; 
		  ocheck pos env x; 
		  match strip_pos(tau env f) with
		  | Expr(TT TT_Pi, [s; Expr(BB w,[t'])]) ->
		      if not ( w = v ) 
		      then raise Error.NotImplemented;
		      overify pos env x s;
		      let env = obind (v,s) env in 
		      tverify pos env t t'
		  | _ -> raise (Error.TypeCheckingFailure(get_pos f,"expected a product type")))
	      | _ -> raise Error.Internal)
	  | OO_lambda -> (
	      match args with 
	      | [t;Expr(BB x,[o])] -> tcheck pos env t; ocheck_binder pos env x t o
	      | _ -> raise Error.Internal)
	  | OO_forall -> (
	      match args with 
	      | [m;m';o;Expr(BB v,[o'])] ->
		  ucheck pos env m; 
		  ucheck pos env m'; 	(* probably have to check something here ... *)
		  ocheck pos env o; 
		  ocheck_binder pos env v (Expr(TT TT_El, [o])) o'
	      | _ -> raise Error.Internal)
	  | OO_def_app d -> ()
	  | OO_numeral i -> ()
	  | OO_pair -> raise Error.NotImplemented
	  | OO_pr1 -> raise Error.NotImplemented
	  | OO_pr2 -> raise Error.NotImplemented
	  | OO_total -> raise Error.NotImplemented
	  | OO_pt -> raise Error.NotImplemented
	  | OO_pt_r -> raise Error.NotImplemented
	  | OO_tt -> raise Error.NotImplemented
	  | OO_coprod -> raise Error.NotImplemented
	  | OO_ii1 -> raise Error.NotImplemented
	  | OO_ii2 -> raise Error.NotImplemented
	  | OO_sum -> raise Error.NotImplemented
	  | OO_empty -> raise Error.NotImplemented
	  | OO_empty_r -> raise Error.NotImplemented
	  | OO_c -> raise Error.NotImplemented
	  | OO_ic_r -> raise Error.NotImplemented
	  | OO_ic -> raise Error.NotImplemented
	  | OO_paths -> raise Error.NotImplemented
	  | OO_refl -> raise Error.NotImplemented
	  | OO_J -> raise Error.NotImplemented
	  | OO_rr0 -> raise Error.NotImplemented
	  | OO_rr1 -> raise Error.NotImplemented
	 )
     )
and tcheck_binder pos env x t1 t2 =
  let env = obind (x,t1) env in
  tcheck pos env t2
and ocheck_binder pos env x t o =
  let env = obind (x,t) env in
  ocheck pos env o
and ucheckn i pos env a =
  if i != List.length a then raise Error.Internal;
  List.iter (ucheck pos env) a
and tcheckn i pos env a =
  if i != List.length a then raise Error.Internal;
  List.iter (tcheck pos env) a
and ocheckn i pos env a =
  if i != List.length a then raise Error.Internal;
  List.iter (ocheck pos env) a
and ucheckl pos env a = List.iter (ucheck pos env) a
and tcheckl pos env a = List.iter (tcheck pos env) a
and ocheckl pos env a = List.iter (ocheck pos env) a
and overify pos env o t =			(* verify that o has type t *)
  let t' = (tau env o) in
  if not (equal t' t)
  then raise (Error.TypeCheckingFailure3 (get_pos o, "expected term "^(Printer.etostring o),
				   get_pos t', "of type "^(Printer.etostring t'),
				   get_pos t , "to have type "^(Printer.etostring t)))
and tverify pos env t1 t2 =			(* verify that t1 = t2 *)
  if not (equal t1 t2)
  then raise (Error.TypeCheckingFailure3 (get_pos t2, "expected equal types",
				   get_pos t1,"first type: " ^ (Printer.etostring t1),
				   get_pos t2,"other type: " ^ (Printer.etostring t2)))
  else ()      

let ucheck = ucheck Error.Nowhere
let tcheck = tcheck Error.Nowhere
let ocheck = ocheck Error.Nowhere
let uexprcheck = uexprcheck Error.Nowhere

let ucheck_okay env x = try ucheck env x; true with Error.TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with Error.TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with Error.TypeCheckingFailure _ -> false
