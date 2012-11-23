open Typesystem
open Tau
open Equality

let rec ucheck pos env = function
    | POS(pos,e) -> (
	match e with
	| Variable Var s -> (
	    match (
	      try List.assoc s env.lookup_order
	      with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound u-variable: "^s)))
	    with 
	      (_,Ulevel_variable) -> ()
	    | (_,Type_variable) -> raise (Error.TypeCheckingFailure (pos, "expected a u-variable but found a t-variable: "^s))
	    | (_,Object_variable) -> raise (Error.TypeCheckingFailure (pos, "expected a u-variable but found an o-variable: "^s)))
	| APPLY(UU UU_plus n, [u]) -> ucheck pos env u
	| APPLY(UU UU_max, [u;v]) -> ucheck pos env u;ucheck pos env v
	| APPLY(UU UU_def_app _, _) -> raise Error.NotImplemented
	| _ -> raise Error.Internal)
    | _ -> raise Error.Internal

let rec tcheck pos env = function
    | LAMBDA _ -> raise Error.Internal
    | POS(pos,e) -> match e with 
      | Variable Var s -> (
	  match (
	    try List.assoc s env.lookup_order
	    with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound t-variable: "^s)))
	  with 
	    (_,Ulevel_variable) -> raise (Error.TypeCheckingFailure (pos, "expected a t-variable but found a u-variable: "^s))
	  | (_,Type_variable) -> ()
	  | (_,Object_variable) -> raise (Error.TypeCheckingFailure (pos, "expected a t-variable but found an o-variable: "^s)))
      | Variable _ -> raise Error.Internal
      | APPLY(h,args) -> match h with
	| TT th -> (
	    match th with 
	    | TT_EmptyHole -> raise (Error.TypeCheckingFailure(pos,"empty hole for t-expression found"))
	    | TT_El -> ocheckn 1 pos env args
	    | TT_U -> ucheckn 1 pos env args
	    | TT_Sigma | TT_Pi -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> tcheck pos env t1; tcheck_binder pos env x t1 t2
		| _ -> raise Error.Internal)
	    | TT_Pt -> ()
	    | TT_Coprod -> (
		match args with
		| [t1; t2] -> tcheck pos env t1; tcheck pos env t2
		| _ -> raise Error.Internal)
	    | TT_Coprod2 -> (
		match args with 
		| [t;t'; LAMBDA( x,u);LAMBDA( x', u');o] -> raise Error.NotImplemented
		| _ -> raise Error.Internal)
	    | TT_Empty -> ()
	    | TT_IC -> raise Error.NotImplemented
	    | TT_Id -> (
		match args with
		| [t; x; y] -> (
		    tcheck pos env t; ocheck pos env x; ocheck pos env y; 
		    overify pos env x t; overify pos env y t)
		| _ -> raise Error.Internal)
	    | TT_def_app d -> raise Error.NotImplemented
	   )
	| UU _ -> raise (Error.TypeCheckingFailure(pos, "expected a t-expression but found a u-expression"))
	| OO _ -> raise (Error.TypeCheckingFailure(pos, "expected a t-expression but found an o-expression"))
and ocheck pos env = function
  | LAMBDA _ -> raise Error.Internal	(* should have been handled higher up *)
  | POS(pos,e) -> match e with
    | Variable Var s -> (
	match
	  try List.assoc s env.lookup_order
	  with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound o-variable: "^s))
	with 
	  (_,Ulevel_variable) -> raise (Error.TypeCheckingFailure (pos, "expected an o-variable but found a u-variable: "^s))
	| (_,Type_variable) -> raise (Error.TypeCheckingFailure (pos, "expected an o-variable but found a t-variable: "^s))
	| (_,Object_variable) -> ())
    | Variable (VarGen _ | VarUnused | VarEmptyHole) -> raise Error.Internal
    | APPLY(h,args) -> match h with
      | UU th -> raise (Error.TypeCheckingFailure(pos, "expected an o-expression but found a u-expression"))
      | TT th -> raise (Error.TypeCheckingFailure(pos, "expected an o-expression but found a t-expression"))
      | OO oh -> match oh with
	| OO_emptyHole -> raise Error.Internal
	| OO_u -> ucheckn 1 pos env args
	| OO_j -> ucheckn 2 pos env args
	| OO_ev -> (
	    match args with 
	    | [f;o] -> raise Error.Internal (* type should have been filled in by now *)
	    | [f;x;LAMBDA( v,t)] -> (
		ocheck pos env f; 
		ocheck pos env x; 
		match strip_pos(tau env f) with
		| APPLY(TT TT_Pi, [s; LAMBDA( w,t')]) ->
		    if not ( w = v ) 
		    then raise Error.NotImplemented;
		    overify pos env x s;
		    let env = obind (v,s) env in 
		    tverify pos env t t'
		| _ -> raise (Error.TypeCheckingFailure(get_pos f,"expected a product type")))
	    | _ -> raise Error.Internal)
	| OO_lambda -> (
	    match args with 
	    | [t;LAMBDA( x,o)] -> tcheck pos env t; ocheck_binder pos env x t o
	    | _ -> raise Error.Internal)
	| OO_forall -> (
	    match args with 
	    | [m;m';o;LAMBDA( v,o')] ->
		ucheck pos env m; 
		ucheck pos env m'; 	(* probably have to check something here ... *)
		ocheck pos env o; 
		ocheck_binder pos env v (with_pos_of o (APPLY(TT TT_El, [o]))) o'
	    | _ -> raise Error.Internal)
	| OO_def_app d -> ()
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

let ucheck_okay env x = try ucheck env x; true with Error.TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with Error.TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with Error.TypeCheckingFailure _ -> false
