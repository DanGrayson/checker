open Typesystem
open Tau
open Equality
exception TypeCheckingFailure of position * string
exception TypeCheckingFailure2 of position * string * position * string
exception TypeCheckingFailure3 of position * string * position * string * position * string

let rec uexprcheck pos env = 
  let rec ucheckexpr' env = function
    | Upos (pos,u) -> uexprcheck pos env u
    | Uvariable UVar s -> (
	match (
	  try List.assoc s env.lookup_order
	  with Not_found -> raise (TypeCheckingFailure (pos, "encountered unbound u-variable: "^s)))
	with 
	  U _ -> ()
	| T _ -> raise (TypeCheckingFailure (pos, "expected a u-variable but found a t-variable: "^s))
	| O _ -> raise (TypeCheckingFailure (pos, "expected a u-variable but found an o-variable: "^s)))
    | Uplus (u,n) -> ucheckexpr' env u
    | Umax (u,v) -> ucheckexpr' env u; ucheckexpr' env v
    | U_def _ -> raise NotImplemented
    | UEmptyHole | UNumberedEmptyHole _ -> raise (TypeCheckingFailure(pos, "empty hole for u-expression found"))
  in ucheckexpr' env

let rec ucheck pos env =
  let rec ucheck' env = function
    | POS(pos,e) -> ucheck pos env e
    | UU u -> uexprcheck pos env u
    | _ -> raise InternalError
  in ucheck' env

let rec tcheck pos env = 
  let rec tcheck' env = function
    | POS(pos,e) -> tcheck pos env e
    | UU u -> uexprcheck pos env u
    | TT_variable TVar s -> (
	match (
	  try List.assoc s env.lookup_order
	  with Not_found -> raise (TypeCheckingFailure (pos, "encountered unbound t-variable: "^s)))
	with 
	  U _ -> raise (TypeCheckingFailure (pos, "expected a t-variable but found a u-variable: "^s))
	| T _ -> ()
	| O _ -> raise (TypeCheckingFailure (pos, "expected a t-variable but found an o-variable: "^s)))
    | OO_variable o -> raise InternalError
    | Expr(h,args) -> (
	match h with
	| BB x -> raise InternalError
	| TT th -> (
	    match th with 
	    | TT_EmptyHole | TT_NumberedEmptyHole _ -> raise (TypeCheckingFailure(pos,"empty hole for t-expression found"))
	    | TT_El -> ocheckn 1 pos env args
	    | TT_U -> ucheckn 1 pos env args
	    | TT_Sigma | TT_Pi -> (
		match args with
		| [t1; Expr( BB x, [t2] )] -> tcheck' env t1; tcheck_binder pos env x t1 t2
		| _ -> raise InternalError)
	    | TT_Pt -> ()
	    | TT_Coprod -> (
		match args with
		| [t1; t2] -> tcheck' env t1; tcheck' env t2
		| _ -> raise InternalError)
	    | TT_Coprod2 -> (
		match args with 
		| [t;t'; Expr(BB x,[u]);Expr(BB x', [u']);o] -> raise NotImplemented
		| _ -> raise InternalError)
	    | TT_Empty -> ()
	    | TT_IC -> (
		match args with [tA; a; Expr(BB x, [tB;Expr( BB y, [tD;Expr( BB z, [q])])])] -> raise NotImplemented
		| _ -> raise InternalError)
	    | TT_Id -> (
	      match args with
	      | [t; x; y] -> (
		  tcheck' env t; ocheck pos env x; ocheck pos env y; 
		  overify pos env x t; overify pos env y t)
	      | _ -> raise InternalError)
	    | TT_def_app d -> raise NotImplemented
	    | TT_nat -> ()
	   )
	| OO _ -> raise (TypeCheckingFailure(pos, "expected a t-expression but found an o-expression"))
       )
  in tcheck' env
and ocheck pos env = function
  | POS(pos,e) -> ()
  | UU u -> ()
  | TT_variable t -> ()
  | OO_variable OVarGen (i,s) -> raise NotImplemented
  | OO_variable OVarUnused -> raise InternalError
  | OO_variable OVarEmptyHole -> raise InternalError
  | OO_variable OVar s -> (
      match
	try List.assoc s env.lookup_order
	with Not_found -> raise (TypeCheckingFailure (pos, "encountered unbound o-variable: "^s))
      with 
	U _ -> raise (TypeCheckingFailure (pos, "expected an o-variable but found a u-variable: "^s))
      | T _ -> raise (TypeCheckingFailure (pos, "expected an o-variable but found a t-variable: "^s))
      | O _ -> ())
  | Expr(h,args) -> (
      match h with
      | BB x -> raise InternalError	(* should have been handled higher up *)
      | TT th -> raise (TypeCheckingFailure(pos, "expected an o-expression but found a t-expression"))
      | OO oh -> (
	  match oh with
	  | OO_emptyHole | OO_numberedEmptyHole _ -> raise InternalError
	  | OO_u -> ucheckn 1 pos env args
	  | OO_j -> ucheckn 2 pos env args
	  | OO_ev -> (
	      match args with 
	      | [f;o] -> raise InternalError (* type should have been filled in by now *)
	      | [f;x;Expr(BB v,[t])] -> (
		  ocheck pos env f; 
		  ocheck pos env x; 
		  match strip_pos(tau env f) with
		  | Expr(TT TT_Pi, [s; Expr(BB w,[t'])]) ->
		      if not ( w = v ) 
		      then raise (
			TypeCheckingFailure(pos,"expected identical variables: " ^
					    (Printer.ovartostring w) ^ ", " ^
					    (Printer.ovartostring v) ^ ")"));
		      overify pos env x s;
		      let env = obind (v,s) env in 
		      tverify pos env t t'
		  | _ -> raise (TypeCheckingFailure(get_pos f,"expected a product type")))
	      | _ -> raise InternalError)
	  | OO_lambda -> (
	      match args with 
	      | [t;Expr(BB x,[o])] -> tcheck pos env t; ocheck_binder pos env x t o
	      | _ -> raise InternalError)
	  | OO_forall -> (
	      match args with 
	      | [m;m';o;Expr(BB v,[o'])] ->
		  ucheck pos env m; 
		  ucheck pos env m'; 	(* probably have to check something here ... *)
		  ocheck pos env o; 
		  ocheck_binder pos env v (Expr(TT TT_El, [o])) o'
	      | _ -> raise InternalError)
	  | OO_def_app d -> ()
	  | OO_numeral i -> ()
	  | OO_pair -> raise NotImplemented
	  | OO_pr1 -> raise NotImplemented
	  | OO_pr2 -> raise NotImplemented
	  | OO_total -> raise NotImplemented
	  | OO_pt -> raise NotImplemented
	  | OO_pt_r -> raise NotImplemented
	  | OO_tt -> raise NotImplemented
	  | OO_coprod -> raise NotImplemented
	  | OO_ii1 -> raise NotImplemented
	  | OO_ii2 -> raise NotImplemented
	  | OO_sum -> raise NotImplemented
	  | OO_empty -> raise NotImplemented
	  | OO_empty_r -> raise NotImplemented
	  | OO_c -> raise NotImplemented
	  | OO_ic_r -> raise NotImplemented
	  | OO_ic -> raise NotImplemented
	  | OO_paths -> raise NotImplemented
	  | OO_refl -> raise NotImplemented
	  | OO_J -> raise NotImplemented
	  | OO_rr0 -> raise NotImplemented
	  | OO_rr1 -> raise NotImplemented
	 )
     )
and tcheck_binder pos env x t1 t2 =
  let env = obind (x,t1) env in
  tcheck pos env t2
and ocheck_binder pos env x t o =
  let env = obind (x,t) env in
  ocheck pos env o
and ucheckn i pos env a =
  if i != List.length a then raise InternalError;
  List.iter (ucheck pos env) a
and tcheckn i pos env a =
  if i != List.length a then raise InternalError;
  List.iter (tcheck pos env) a
and ocheckn i pos env a =
  if i != List.length a then raise InternalError;
  List.iter (ocheck pos env) a
and ucheckl pos env a = List.iter (ucheck pos env) a
and tcheckl pos env a = List.iter (tcheck pos env) a
and ocheckl pos env a = List.iter (ocheck pos env) a
and overify pos env o t =			(* verify that o has type t *)
  let t' = (tau env o) in
  if not (tequal t' t)
  then raise (TypeCheckingFailure3 (get_pos o, "expected term "^(Printer.etostring o),
				   get_pos t', "of type "^(Printer.etostring t'),
				   get_pos t , "to have type "^(Printer.etostring t)))
and tverify pos env t1 t2 =			(* verify that t1 = t2 *)
  if not (tequal t1 t2)
  then raise (TypeCheckingFailure3 (get_pos t2, "expected equal types",
				   get_pos t1,"first type: " ^ (Printer.etostring t1),
				   get_pos t2,"other type: " ^ (Printer.etostring t2)))
  else ()      

let ucheck = ucheck Nowhere
let tcheck = tcheck Nowhere
let ocheck = ocheck Nowhere
let uexprcheck = uexprcheck Nowhere

let ucheck_okay env x = try ucheck env x; true with TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with TypeCheckingFailure _ -> false
