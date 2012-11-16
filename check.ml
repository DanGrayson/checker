(** In this file we do typechecking.  

    For a t-expression, this just amounts to being well-formed, since types
    have no type.  For an o-expression, it's a meta-theorem that the type turns
    out to equal the result that the function tau yields.  The body of a
    definition is checked in its local context, as a t-expression or as an
    o-expression; it's a meta-theorem that later substitution preserves types,
    so unfolding of o-definitions embedded in other expressions is not needed
    at the point they are encounted, as the type of the result obtained by
    unfolding is more easily obtained by substitution; unfolding of
    t-definitions may be required to overify definitional equality between two
    types, and that, in turn, may lead to embedded uses of o-definitions
    getting unfolded and normalized.  

    Type checking a variable amounts to checking that it is in scope, which
    means it is looked up by name in the current context to see if the result
    is a variable of the same type: u, t, or o.  (The parser can infer from the
    grammar whether a variable is a t-variable, o-variable, or u-variable, but
    the parser ignores the environment.

    This version of the type checker will not handle undecidable aspects of
    definitional equality and will not produce a derivation tree.  Probably it
    can be enhanced to do so, perhaps by returning a closure that can be stored
    in an expression, which, when called later, will produce the derivation
    tree.

    Still to do: add type equality checking to the cases that require it.

    Failure to type is signaled with an exception. *)

open Typesystem
open Tau
open Equality
exception TypeCheckingFailure of position * string

let rec ucheck (env:environment_type) u = match strip_pos u with
  | Uvariable UVar s -> (
      match (
	try List.assoc s env.lookup_order
	with Not_found -> raise (TypeCheckingFailure (get_pos u, "encountered unbound u-variable: "^s)))
      with 
	U _ -> ()
      | T _ -> raise (TypeCheckingFailure (get_pos u, "expected a u-variable but found a t-variable: "^s))
      | O _ -> raise (TypeCheckingFailure (get_pos u, "expected a u-variable but found an o-variable: "^s)))
  | Uplus (u,n) -> ucheck env u
  | Umax (u,v) -> ucheck env u; ucheck env v
  | UEmptyHole
  | UNumberedEmptyHole _ -> raise (TypeCheckingFailure(get_pos u, "empty hole for u-expression found"))
  | U_def _ -> raise (TypingUnimplemented (get_pos u, "u-definition"))

let rec tcheck (env:environment_type) t = match strip_pos t with
    Tvariable TVar s -> (
      match (
	try List.assoc s env.lookup_order
	with Not_found -> raise (TypeCheckingFailure (get_pos t, "encountered unbound t-variable: "^s)))
      with 
	U _ -> raise (TypeCheckingFailure (get_pos t, "expected a t-variable but found a u-variable: "^s))
      | T _ -> ()
      | O _ -> raise (TypeCheckingFailure (get_pos t, "expected a t-variable but found an o-variable: "^s)))
  | TEmptyHole | TNumberedEmptyHole _ -> raise (TypeCheckingFailure(get_pos t,"empty hole for t-expression found"))
  | El o -> ocheck env o
  | T_U _ -> ()
  | Pi (t1,(v,t2)) -> tcheck env t1; tcheck_binder (obind (strip_pos v,t1) env) (v,t2)
  | Sigma (t1,(v,t2)) -> tcheck env t1; tcheck_binder (obind (strip_pos v,t1) env) (v,t2)
  | T_Pt -> ()
  | T_Coprod (t1,t2) -> tcheck env t1; tcheck env t2
  | T_Coprod2 (t1,t2,(x,u),(x',u'),o) -> 
      tcheck env t1; tcheck env t2; tcheck_binder env (x,u); tcheck_binder env (x',u'); ocheck env o;
      raise (TypingUnimplemented (get_pos t, "coprod"))
  | T_Empty -> ()
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> 
      tcheck env tA; ocheck env a; ttocheck_binder env (x,tB,(y,tD,(z,q)));
      raise (TypingUnimplemented (get_pos t, "IC"))
  | Id (t,x,y) -> tcheck env t; ocheck env x; ocheck env y; overify env x t; overify env y t
  | T_def (d,u,t',o) -> 
      List.iter (ucheck env) u; List.iter (tcheck env) t'; List.iter (ocheck env) o; 
      raise (TypingUnimplemented (get_pos t, "t-definition"))
  | T_nat -> ()
and overify env o t =			(* verify that o has type t *)
  let t' = (tau env o) in
  if not (tequal t' t)
  then raise (TypeCheckingFailure (get_pos o, 
				   "expected "^
				   "\n           term "^(Printer.otostring o)^
				   "\n        of type "^(Printer.ttostring t')^
				   "\n   to have type "^(Printer.ttostring t)))
and tverify env t1 t2 =			(* verify that t1 = t2 *)
  if not (tequal t1 t2)
  then raise (TypeCheckingFailure (get_pos t2, "expected equal types:\n"^
				   "     : "^(Printer.ttostring t1) ^ "\n" ^
				   "     : "^(Printer.ttostring t2)
				  ))
  else ()      
and ocheck (env:environment_type) o = match strip_pos o with
  Ovariable OVar s -> (
    match
      try List.assoc s env.lookup_order
      with Not_found -> raise (TypeCheckingFailure (get_pos o, "encountered unbound o-variable: "^s))
    with 
      U _ -> raise (TypeCheckingFailure (get_pos o, "expected an o-variable but found a u-variable: "^s))
    | T _ -> raise (TypeCheckingFailure (get_pos o, "expected an o-variable but found a t-variable: "^s))
    | O _ -> ())
  | Ovariable OVarGen (i,s) -> ()
  | Ovariable OVarUnused -> raise InternalError
  | Ovariable OVarEmptyHole -> raise InternalError
  | Onumeral _ -> ()
  | OEmptyHole | ONumberedEmptyHole _ -> raise (TypeCheckingFailure(get_pos o,"empty o-expression hole, no method for filling"))
  | O_u u -> ucheck env u
  | O_j (u,v) -> ucheck env u; ucheck env v
  | O_ev(f,x,(v,t)) -> (
      ocheck env f; 
      ocheck env x; 
      match strip_pos(tau env f) with
	| Pi(s,(w,t')) -> 
	    if not ( w = v ) 
	    then raise (
	      TypeCheckingFailure(get_pos o,"expected identical variables: " ^
				  (Printer.ovartostring w) ^ ", " ^
				  (Printer.ovartostring v) ^ ")"));
	    overify env x s;
	    let env = obind (strip_pos v,s) env in 
	    tverify env t t'
	| _ -> raise (TypeCheckingFailure(get_pos f,"expected a product type")))
  | O_lambda (t,(v,p)) -> tcheck env t; ocheck_binder (obind (strip_pos v,t) env) (v,p)
  | O_forall (m,m',o,(v,o')) -> ucheck env m; ucheck env m'; ocheck env o; ocheck_binder (obind (strip_pos v,nowhere(El o)) env) (v,o')
  | O_pair (a,b,(x,t)) -> ocheck env a; ocheck env b; tcheck_binder env (x,t)
  | O_pr1 (t,(x,t'),o) -> tcheck env t; tcheck_binder env (x,t'); ocheck env o
  | O_pr2 (t,(x,t'),o) -> tcheck env t; tcheck_binder env (x,t'); ocheck env o
  | O_total (m1,m2,o1,(x,o2)) -> ucheck env m1; ucheck env m2; ocheck env o1; ocheck_binder env (x,o2)
  | O_pt -> ()
  | O_pt_r (o,(x,t)) -> ocheck env o; tcheck_binder (obind (strip_pos x,nowhere T_Pt) env) (x,t)
  | O_tt -> ()
  | O_coprod (m1,m2,o1,o2) -> ucheck env m1; ucheck env m2; ocheck env o1; ocheck env o2
  | O_ii1 (t,t',o) -> tcheck env t; tcheck env t'; ocheck env o
  | O_ii2 (t,t',o) -> tcheck env t; tcheck env t'; ocheck env o
  | Sum (tT,tT',s,s',o,(x,tS)) -> tcheck env tT; tcheck env tT'; ocheck env s; ocheck env s'; ocheck env o; tcheck_binder env (x,tS)
  | O_empty -> ()
  | O_empty_r (t,o) -> tcheck env t; ocheck env o
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f) -> tcheck env tA; ocheck env a; ttocheck_binder env (x,tB,(y,tD,(z,q))); ocheck env b; ocheck env f
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) 
    -> tcheck env tA; ocheck env a; ttocheck_binder env (x,tB,(y,tD,(z,q))); ocheck env i; t2check_binder env (x',v,tS); ocheck env t
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))) -> ucheck env m1; ucheck env m2; ucheck env m3; ocheck env oA; ocheck env a; ooocheck_binder env (x,oB,(y,oD,(z,q)))
  | O_paths (m,t,x,y) -> ucheck env m; ocheck env t; ocheck env x; ocheck env y
  | O_refl (t,o) -> tcheck env t; ocheck env o
  | O_J (tT,a,b,q,i,(x,e,tS)) -> tcheck env tT; ocheck env a; ocheck env b; ocheck env q; ocheck env i; t2check_binder env (x,e,tS)
  | O_rr0 (m2,m1,s,t,e) -> ucheck env m2; ucheck env m1; ocheck env s; ocheck env t; ocheck env e
  | O_rr1 (m,a,p) -> ucheck env m; ocheck env a; ocheck env p
  | O_def (d,u,t,o) -> List.iter (ucheck env) u; List.iter (tcheck env) t; List.iter (ocheck env) o;
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

let ucheck_okay env x = try ucheck env x; true with TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with TypeCheckingFailure _ -> false
