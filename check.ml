open Typesystem
open Tau
open Equality

let rec ucheck pos env (pos,e) = match e with 
  | EmptyHole _ -> raise (Error.TypeCheckingFailure (pos, "encountered empty hole, but expected a u-expression"))
  | Variable v -> (
      let t = 
	try List.assoc (LF_Var v) env
	with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound u-variable: "^(vartostring' v)))
      in
      if t != uexp then raise (Error.TypeCheckingFailure (pos, "expected a u-variable: "^(vartostring' v))))
  | APPLY(U U_next, [ATOMIC u]) -> ucheck pos env u
  | APPLY(U U_max, [ATOMIC u;ATOMIC v]) -> ucheck pos env u;ucheck pos env v
  | _ -> raise Error.Internal

let rec tcheck pos env ((pos,e0) as e) = match e0 with
  | EmptyHole _ -> raise (Error.TypeCheckingFailure (pos, "encountered empty hole, but expected a t-expression"))
  | Variable v ->(
      let t =
	try List.assoc (LF_Var v) env
	with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound t-variable: "^(vartostring' v)))
      in if t != texp then raise (Error.TypeCheckingFailure (pos, "expected a t-variable: "^(vartostring' v))))
  | APPLY(h,args) -> match h with
    | L _ -> raise (Unimplemented_expr (ATOMIC e))
    | R _ -> raise Error.NotImplemented
    | T th -> (
	match th with 
	| T_El -> (match args with
	    [ATOMIC u] -> ocheck pos env u
	    | _ -> raise Error.Internal)
	| T_U -> (match args with
	    [ATOMIC u] -> ucheck pos env u
	    | _ -> raise Error.Internal)
	| T_Sigma | T_Pi -> (
	    match args with
	    | [ATOMIC t1; LAMBDA( x, ATOMIC t2 )] -> tcheck pos env t1; tcheck_binder pos env x t1 t2
	    | _ -> raise Error.Internal)
	| T_Pt -> ()
	| T_Coprod -> (
	    match args with
	    | [ATOMIC t1; ATOMIC t2] -> tcheck pos env t1; tcheck pos env t2
	    | _ -> raise Error.Internal)
	| T_Coprod2 -> (
	    match args with 
	    | [ATOMIC t;ATOMIC t'; LAMBDA( x,ATOMIC u);LAMBDA( x', ATOMIC u');ATOMIC o] -> raise Error.NotImplemented
	    | _ -> raise Error.Internal)
	| T_Empty -> ()
	| T_IC -> raise Error.NotImplemented
	| T_Id -> (
	    match args with
	    | [ATOMIC t; ATOMIC x; ATOMIC y] -> (
		tcheck pos env t; ocheck pos env x; ocheck pos env y; 
		overify pos env x t; overify pos env y t)
	    | _ -> raise Error.Internal)
       )
    | U _ -> raise (Error.TypeCheckingFailure(pos, "expected a t-expression but found a u-expression"))
    | O _ -> raise (Error.TypeCheckingFailure(pos, "expected a t-expression but found an o-expression"))

and ocheck pos env ((pos,e0) as e) = 
  match e0 with 
  | EmptyHole _ -> raise (Error.TypeCheckingFailure (pos, "encountered empty hole, but expected a o-expression"))
  | Variable v -> (
      let t = (
	try List.assoc (LF_Var v) env
	with Not_found -> raise (Error.TypeCheckingFailure (pos, "encountered unbound o-variable: "^(vartostring' v))))
      in if t != oexp then raise (Error.TypeCheckingFailure (pos, "expected an o-variable: "^(vartostring' v))))
  | APPLY(h,args) -> match h with
    | L _ -> raise (Unimplemented_expr (ATOMIC e))
    | R _ -> raise Error.NotImplemented
    | U th -> raise (Error.TypeCheckingFailure(pos, "expected an o-expression but found a u-expression"))
    | T th -> raise (Error.TypeCheckingFailure(pos, "expected an o-expression but found a t-expression"))
    | O oh -> match oh with
      | O_u -> (match args with
	    [ATOMIC u] -> ucheck pos env u
	    | _ -> raise Error.Internal)
      | O_j -> (match args with
	    [ATOMIC u;ATOMIC v] -> ucheck pos env u;ucheck pos env v
	    | _ -> raise Error.Internal)
      | O_ev -> (
	  match args with 
	  | [ATOMIC f;ATOMIC o] -> raise Error.Internal (* type should have been filled in by now *)
	  | [ATOMIC f;ATOMIC x;LAMBDA( v,ATOMIC t)] -> (
	      ocheck pos env f; 
	      ocheck pos env x; 
	      match strip_pos(tau env f) with
	      | APPLY(T T_Pi, [ATOMIC s; LAMBDA( w,ATOMIC t')]) ->
		  if not ( (strip_pos w) = (strip_pos v) ) 
		  then raise Error.NotImplemented;
		  overify pos env x s;
		  let env = ts_bind (v, s) env in 
		  tverify pos env t t'
	      | _ -> raise (Error.TypeCheckingFailure(get_pos f,"expected a function type")))
	  | _ -> raise Error.Internal)
      | O_lambda -> (
	  match args with 
	  | [ATOMIC t;LAMBDA(x,ATOMIC o)] -> tcheck pos env t; ocheck_binder pos env x t o
	  | _ -> raise Error.Internal)
      | O_forall -> (
	  match args with 
	  | [ATOMIC m;ATOMIC m';ATOMIC o;LAMBDA( v,ATOMIC o')] ->
	      ucheck pos env m; 
	      ucheck pos env m'; 	(* probably have to check something here ... *)
	      ocheck pos env o; 
	      ocheck_binder pos env v (with_pos_of o (APPLY(T T_El, [ATOMIC o]))) o'
	  | _ -> raise Error.Internal)
      | O_pair -> raise Error.NotImplemented
      | O_pr1 -> raise Error.NotImplemented
      | O_pr2 -> raise Error.NotImplemented
      | O_total -> raise Error.NotImplemented
      | O_pt -> raise Error.NotImplemented
      | O_pt_r -> raise Error.NotImplemented
      | O_tt -> raise Error.NotImplemented
      | O_coprod -> raise Error.NotImplemented
      | O_ii1 -> raise Error.NotImplemented
      | O_ii2 -> raise Error.NotImplemented
      | O_sum -> raise Error.NotImplemented
      | O_empty -> raise Error.NotImplemented
      | O_empty_r -> raise Error.NotImplemented
      | O_c -> raise Error.NotImplemented
      | O_ic_r -> raise Error.NotImplemented
      | O_ic -> raise Error.NotImplemented
      | O_paths -> raise Error.NotImplemented
      | O_refl -> raise Error.NotImplemented
      | O_J -> raise Error.NotImplemented
      | O_rr0 -> raise Error.NotImplemented
      | O_rr1 -> raise Error.NotImplemented
and tcheck_binder pos env x t1 t2 =
  let env = ts_bind (x, t1) env in
  tcheck pos env t2
and ocheck_binder pos env x t o =
  let env = ts_bind (x, t) env in
  ocheck pos env o
and tcheckn i pos env a =
  if i != List.length a then raise Error.Internal;
  List.iter (tcheck pos env) a
and ucheckl pos env a = List.iter (ucheck pos env) a
and tcheckl pos env a = List.iter (tcheck pos env) a
and ocheckl pos env a = List.iter (ocheck pos env) a
and overify pos env o t =			(* verify that o has type t *)
  let t' = (tau env o) in
  if not (equal t' t)
  then raise (Error.TypeCheckingFailure3 (get_pos o, "expected term "^(Printer.ts_expr_to_string o),
				   get_pos t', "of type "^(Printer.ts_expr_to_string t'),
				   get_pos t , "to have type "^(Printer.ts_expr_to_string t)))
and tverify pos env t1 t2 =			(* verify that t1 = t2 *)
  if not (equal t1 t2)
  then raise (Error.TypeCheckingFailure3 (get_pos t2, "expected equal types",
				   get_pos t1,"first type: " ^ (Printer.ts_expr_to_string t1),
				   get_pos t2,"other type: " ^ (Printer.ts_expr_to_string t2)))
  else ()      

let ucheck = ucheck Error.Nowhere
let tcheck = tcheck Error.Nowhere
let ocheck = ocheck Error.Nowhere

let ucheck_okay env x = try ucheck env x; true with Error.TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with Error.TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with Error.TypeCheckingFailure _ -> false
