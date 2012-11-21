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
	    | TT_El -> ocheckl pos env args
	    | TT_U -> ucheckn 1 pos env args
	    | TT_Pi -> (
		match args with
		| [t1; Expr( BB x, [t2] )] -> ()
		| _ -> raise InternalError)
	    | TT_Sigma -> (
		match args with [t1; Expr( BB x, [t2] )] -> ()
		| _ -> raise InternalError)
	    | TT_Pt -> ()
	    | TT_Coprod -> ()
	    | TT_Coprod2 -> (
		match args with 
		| [t;t'; Expr(BB x,[u]);Expr(BB x', [u']);o] -> ()
		| _ -> raise InternalError)
	    | TT_Empty -> ()
	    | TT_IC -> (
		match args with [tA; a; Expr(BB x, [tB;Expr( BB y, [tD;Expr( BB z, [q])])])] -> ()
		| _ -> raise InternalError)
	    | TT_Id -> ()
	    | TT_def_app d -> ()
	    | TT_nat -> ()
	   )
	| OO oh -> (
	    match oh with
	    | OO_emptyHole -> ()
	    | OO_numberedEmptyHole n -> ()
	    | OO_u -> ()
	    | OO_j -> ()
	    | OO_ev -> (
		match args with 
		| [f;o;Expr(BB x,[t])] -> ()
		| [f;o] -> ()
		| _ -> raise InternalError)
	    | OO_lambda -> (
		match args with 
		| [t;Expr(BB x,[o])] -> ()
		| _ -> raise InternalError)
	    | OO_forall -> (
		match args with 
		| [u;u';o;Expr(BB x,[o'])] -> ()
		| _ -> raise InternalError)
	    | OO_def_app d -> ()
	    | OO_numeral i -> ()
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
  in tcheck' env
and ocheck pos env = function
  | POS(pos,e) -> ()
  | UU u -> ()
  | TT_variable t -> ()
  | OO_variable o -> ()
  | Expr(h,args) -> (
      match h with
      | BB x -> raise InternalError	(* should have been handled higher up *)
      | TT th -> (
	  match th with 
	  | TT_EmptyHole -> ()
	  | TT_NumberedEmptyHole n -> ()
	  | TT_El -> ()
	  | TT_U -> ()
	  | TT_Pi -> (
	      match args with
	      | [t1; Expr( BB x, [t2] )] -> ()
	      | _ -> raise InternalError)
	  | TT_Sigma -> (
	      match args with [t1; Expr( BB x, [t2] )] -> ()
	      | _ -> raise InternalError)
	  | TT_Pt -> ()
	  | TT_Coprod -> ()
	  | TT_Coprod2 -> (
	      match args with 
	      | [t;t'; Expr(BB x,[u]);Expr(BB x', [u']);o] -> ()
	      | _ -> raise InternalError)
	  | TT_Empty -> ()
	  | TT_IC -> (
	      match args with [tA; a; Expr(BB x, [tB;Expr( BB y, [tD;Expr( BB z, [q])])])] -> ()
	      | _ -> raise InternalError)
	  | TT_Id -> ()
	  | TT_def_app d -> ()
	  | TT_nat -> ()
	 )
      | OO oh -> (
	  match oh with
	  | OO_emptyHole -> ()
	  | OO_numberedEmptyHole n -> ()
	  | OO_u -> ()
	  | OO_j -> ()
	  | OO_ev -> (
	      match args with 
	      | [f;o;Expr(BB x,[t])] -> ()
	      | [f;o] -> ()
	      | _ -> raise InternalError)
	  | OO_lambda -> (
	      match args with 
	      | [t;Expr(BB x,[o])] -> ()
	      | _ -> raise InternalError)
	  | OO_forall -> (
	      match args with 
	      | [u;u';o;Expr(BB x,[o'])] -> ()
	      | _ -> raise InternalError)
	  | OO_def_app d -> ()
	  | OO_numeral i -> ()
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

(*

let rec tcheck (env:environment_type) t = match strip_pos t with
  | T_El o -> ()
  | T_U _ -> ()
  | T_Pi (t1,(v,t2)) -> 
      tcheck env t1; 
      tcheck_binder (obind (strip_pos v,t1) env) (v,t2)
	(* end of TS0 *)
  | T_Sigma (t1,(v,t2)) -> 
      tcheck env t1; 
      tcheck_binder (obind (strip_pos v,t1) env) (v,t2)
  | T_Pt -> ()
  | T_Coprod (t1,t2) -> tcheck env t1; 
      tcheck env t2
  | T_Coprod2 (t1,t2,(x,u),(x',u'),o) -> 
      tcheck env t1; 
      tcheck env t2; 
      tcheck_binder env (x,u); 
      tcheck_binder env (x',u'); 
      ocheck env o;
      raise (TypingUnimplemented (get_pos t, "coprod"))
  | T_Empty -> ()
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> 
      tcheck env tA; 
      ocheck env a; 
      ttocheck_binder env (x,tB,(y,tD,(z,q)));
      raise (TypingUnimplemented (get_pos t, "IC"))
  | T_Id (t,x,y) -> 
      tcheck env t; 
      ocheck env x; 
      ocheck env y; 
      overify env x t; 
      overify env y t
  | T_def (d,u,t',o) -> 
      List.iter (ucheck env) u; 
      List.iter (tcheck env) t'; 
      List.iter (ocheck env) o; 
      raise (TypingUnimplemented (get_pos t, "t-definition"))
  | T_nat -> ()
and overify env o t =			(* verify that o has type t *)
  let t' = (tau env o) in
  if not (tequal t' t)
  then raise (TypeCheckingFailure3 (get_pos o, "expected term "^(Printer.otostring o),
				   get_pos t', "of type "^(Printer.ttostring t'),
				   get_pos t , "to have type "^(Printer.ttostring t)))
and tverify env t1 t2 =			(* verify that t1 = t2 *)
  if not (tequal t1 t2)
  then raise (TypeCheckingFailure3 (get_pos t2, "expected equal types",
				   get_pos t1,"first type: " ^ (Printer.ttostring t1),
				   get_pos t2,"other type: " ^ (Printer.ttostring t2)))
  else ()      
and ocheck (env:environment_type) o = match strip_pos o with
  O_variable OVar s -> (
    match
      try List.assoc s env.lookup_order
      with Not_found -> raise (TypeCheckingFailure (get_pos o, "encountered unbound o-variable: "^s))
    with 
      U _ -> raise (TypeCheckingFailure (get_pos o, "expected an o-variable but found a u-variable: "^s))
    | T _ -> raise (TypeCheckingFailure (get_pos o, "expected an o-variable but found a t-variable: "^s))
    | O _ -> ())
  | O_variable OVarGen (i,s) -> ()
  | O_variable OVarUnused -> raise InternalError
  | O_variable OVarEmptyHole -> raise InternalError
  | O_numeral _ -> ()
  | O_emptyHole | O_numberedEmptyHole _ -> raise InternalError
  | O_u u -> ucheck env u
  | O_j (u,v) -> ucheck env u; ucheck env v
  | O_ev(f,x,(v,t)) -> (
      ocheck env f; 
      ocheck env x; 
      match strip_pos(tau env f) with
	| T_Pi(s,(w,t')) -> 
	    if not ( w = v ) 
	    then raise (
	      TypeCheckingFailure(get_pos o,"expected identical variables: " ^
				  (Printer.ovartostring w) ^ ", " ^
				  (Printer.ovartostring v) ^ ")"));
	    overify env x s;
	    let env = obind (strip_pos v,s) env in 
	    tverify env t t'
	| _ -> raise (TypeCheckingFailure(get_pos f,"expected a product type")))
  | O_lambda (t,(v,p)) -> 
      tcheck env t; 
      ocheck_binder (obind (strip_pos v,t) env) (v,p)
  | O_forall (m,m',o,(v,o')) -> 
      ucheck env m; 
      ucheck env m'; 
      ocheck env o; 
      ocheck_binder (obind (strip_pos v,with_pos_of o (T_El o)) env) (v,o')
	(* end of TS0 *)
  | O_pair (a,b,(x,t)) -> 
      ocheck env a; 
      ocheck env b; 
      tcheck_binder env (x,t)
  | O_pr1 (t,(x,t'),o) -> 
      tcheck env t; 
      tcheck_binder env (x,t'); 
      ocheck env o
  | O_pr2 (t,(x,t'),o) -> 
      tcheck env t; 
      tcheck_binder env (x,t'); 
      ocheck env o
  | O_total (m1,m2,o1,(x,o2)) -> 
      ucheck env m1; 
      ucheck env m2; 
      ocheck env o1; 
      ocheck_binder env (x,o2)
  | O_pt -> ()
  | O_pt_r (o',(x,t)) -> 
      ocheck env o'; 
      tcheck_binder (obind (strip_pos x,with_pos_of o T_Pt) env) (x,t)
  | O_tt -> ()
  | O_coprod (m1,m2,o1,o2) -> 
      ucheck env m1; 
      ucheck env m2; 
      ocheck env o1; 
      ocheck env o2
  | O_ii1 (t,t',o) -> 
      tcheck env t; 
      tcheck env t'; 
      ocheck env o
  | O_ii2 (t,t',o) -> 
      tcheck env t; 
      tcheck env t'; 
      ocheck env o
  | O_sum (tT,tT',s,s',o,(x,tS)) -> 
      tcheck env tT; 
      tcheck env tT'; 
      ocheck env s; 
      ocheck env s'; 
      ocheck env o; 
      tcheck_binder env (x,tS)
  | O_empty -> ()
  | O_empty_r (t,o) -> 
      tcheck env t; 
      ocheck env o;
      overify env o (nowhere T_Empty)
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f) -> 
      tcheck env tA; 
      ocheck env a; 
      ttocheck_binder env (x,tB,(y,tD,(z,q))); 
      ocheck env b; 
      ocheck env f
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) -> 
      tcheck env tA; 
      ocheck env a; 
      ttocheck_binder env (x,tB,(y,tD,(z,q))); 
      ocheck env i; 
      t2check_binder env (x',v,tS); 
      ocheck env t
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))) -> 
      ucheck env m1; 
      ucheck env m2; 
      ucheck env m3; 
      ocheck env oA; 
      ocheck env a; 
      ooocheck_binder env (x,oB,(y,oD,(z,q)))
  | O_paths (m,t,x,y) -> 
      ucheck env m; 
      ocheck env t; 
      ocheck env x; 
      ocheck env y
  | O_refl (t,o) -> 
      tcheck env t; 
      ocheck env o
  | O_J (tT,a,b,q,i,(x,e,tS)) -> 
      tcheck env tT; 
      ocheck env a; 
      ocheck env b; 
      ocheck env q; 
      ocheck env i; 
      t2check_binder env (x,e,tS)
  | O_rr0 (m2,m1,s,t,e) -> 
      ucheck env m2; 
      ucheck env m1; 
      ocheck env s; 
      ocheck env t; 
      ocheck env e
  | O_rr1 (m,a,p) -> 
      ucheck env m; 
      ocheck env a; 
      ocheck env p
  | O_def (d,u,t,o) -> 
      List.iter (ucheck env) u; 
      List.iter (tcheck env) t; 
      List.iter (ocheck env) o;
and tcheck_binder env (v,t) : unit = 
  let env' = env
  in tcheck env' t
and t2check_binder env (v,w,t) : unit = 
  let env' = env			(*?*) 
  in tcheck env' t
and ocheck_binder env (v,o) : unit = 
  let env' = env			(*?*)
  in ocheck env' o
and oocheck_binder env (v,o,k) : unit =
  let env' = env			(*?*) 
  in ocheck env' o; ocheck_binder env' k
and ooocheck_binder env (v,o,k) : unit = 
  let env' = env			(*?*) 
  in ocheck env' o; oocheck_binder env' k
and tocheck_binder env (v,t,k) : unit = 
  let env' = env			(*?*) 
  in tcheck env t; ocheck_binder env' k
and ttocheck_binder env (v,t,k) : unit = 
  let env' = env			(*?*) 
  in tcheck env t; tocheck_binder env' k

*)

let ucheck = ucheck Nowhere
let tcheck = tcheck Nowhere
let ocheck = ocheck Nowhere
let uexprcheck = uexprcheck Nowhere

let ucheck_okay env x = try ucheck env x; true with TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with TypeCheckingFailure _ -> false
