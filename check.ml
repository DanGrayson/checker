(** In this file we do typechecking.  

    For a t-expression, this just amounts to being well-formed, since types
    have no type.  For an o-expression, it's a meta-theorem that the type turns
    out to equal the result that the function tau yields.  The body of a
    definition is checked in its local context, as a t-expression or as an
    o-expression; it's a meta-theorem that later substitution preserves types,
    so unfolding of o-definitions embedded in other expressions is not needed
    at the point they are encounted, as the type of the result obtained by
    unfolding is more easily obtained by substitution; unfolding of
    t-definitions may be required to verify definitional equality between two
    types, and that, in turn, may lead to embedded uses of o-definitions
    getting unfolded and normalized.  

    Type checking a variable amounts to checking that it is in scope, which
    means it is looked up by name in the current context to see if the result
    is a variable of the same type: u, t, or o.  (The parser can infer from the
    grammar whether a variable is a t-variable, o-variable, or u-variable, but
    the parser ignores the environment.

    This version of the type checker will not handle undecidable aspects of
    definitional equality and will not produce a derivation tree.

    Still to do: add type equality checking to the cases that require it.

    Failure to type is signaled with an exception. *)

open Typesystem
exception TypeCheckingFailure of position * string

let rec ucheck (env:environment_type) (u,pos) = match u with
  | Uvariable UVar s -> (
      match (
	try List.assoc s env.lookup_order
	with Not_found -> raise (TypeCheckingFailure (pos, "encountered unbound u-variable: "^s)))
      with 
	U _ -> ()
      | T _ -> raise (TypeCheckingFailure (pos, "expected a u-variable but found a t-variable: "^s))
      | O _ -> raise (TypeCheckingFailure (pos, "expected a u-variable but found an o-variable: "^s)))
  | Uplus (u,n) -> ucheck env u
  | Umax (u,v) -> ucheck env u; ucheck env v
  | UEmptyHole
  | UNumberedEmptyHole _ -> raise (TypeCheckingFailure(pos, "empty hole for u-expression found"))
  | U_def (d,u) -> raise NotImplemented

let rec tcheck (env:environment_type) (t,pos) = match t with
    Tvariable TVar s -> (
      match (
	try List.assoc s env.lookup_order
	with Not_found -> raise (TypeCheckingFailure (pos, "encountered unbound u-variable: "^s)))
      with 
	U _ -> raise (TypeCheckingFailure (pos, "expected a t-variable but found a u-variable: "^s))
      | T _ -> ()
      | O _ -> raise (TypeCheckingFailure (pos, "expected a t-variable but found an o-variable: "^s)))
  | TEmptyHole | TNumberedEmptyHole _ -> raise (TypeCheckingFailure(pos,"empty hole for t-expression found"))
  | El o -> ocheck env o
  | T_U _ -> ()
  | Pi (t1,(v,t2)) -> tcheck env t1; tcheck_binder (obind (v,t1) env) (v,t2)
  | Sigma (t1,(v,t2)) -> tcheck env t1; tcheck_binder (obind (v,t1) env) (v,t2)
  | T_Pt -> ()
  | T_Coprod (t,t') -> tcheck env t; tcheck env t'
  | T_Coprod2 (t,t',(x,u),(x',u'),o) -> tcheck env t; tcheck env t'; tcheck_binder env (x,u); tcheck_binder env (x',u'); ocheck env o
  | T_Empty -> ()
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> tcheck env tA; ocheck env a; ttocheck_binder env (x,tB,(y,tD,(z,q)))
  | Id (t,x,y) -> tcheck env t; ocheck env x; ocheck env y
  | T_def (d,u,t,o) -> List.iter (ucheck env) u; List.iter (tcheck env) t; List.iter (ocheck env) o; raise NotImplemented (*check d, too*)
  | T_nat -> ()
and ocheck (env:environment_type) (o,pos) = match o with
  Ovariable OVar s -> (
    match
      try List.assoc s env.lookup_order
      with Not_found -> raise (TypeCheckingFailure (pos, "encountered unbound u-variable: "^s))
    with 
      U _ -> raise (TypeCheckingFailure (pos, "expected an o-variable but found a u-variable: "^s))
    | T _ -> raise (TypeCheckingFailure (pos, "expected an o-variable but found a t-variable: "^s))
    | O _ -> ())
  | Ovariable OVarGen (i,s) -> ()
  | Ovariable OVarUnused -> raise InternalError
  | Onumeral _ -> ()
  | OEmptyHole | ONumberedEmptyHole _ -> raise (TypeCheckingFailure(pos,"empty o-expression hole, no method for filling"))
  | O_u u -> ucheck env u
  | O_j (u,v) -> ucheck env u; ucheck env v
  | O_ev(f,p,(OVarUnused,(TEmptyHole,loc))) -> (
    match strip_pos(Tau.tau env f) with
      | Pi(t1,(x,t2)) -> ocheck env f; ocheck env p; tcheck_binder (obind (x,t1) env) (x,t2)
      | _ -> raise (TypeCheckingFailure(get_pos f,"expected a product type"))
    )
  | O_ev(f,p,(v,t)) -> ocheck env f; ocheck env p; tcheck_binder env (v,t)
  | O_lambda (t,(v,p)) -> tcheck env t; ocheck_binder (obind (v,t) env) (v,p)
  | O_forall (m,m',o,(v,o')) -> ucheck env m; ucheck env m'; ocheck env o; ocheck_binder (obind (v,nowhere(El o)) env) (v,o')
  | O_pair (a,b,(x,t)) -> ocheck env a; ocheck env b; tcheck_binder env (x,t)
  | O_pr1 (t,(x,t'),o) -> tcheck env t; tcheck_binder env (x,t'); ocheck env o
  | O_pr2 (t,(x,t'),o) -> tcheck env t; tcheck_binder env (x,t'); ocheck env o
  | O_total (m1,m2,o1,(x,o2)) -> ucheck env m1; ucheck env m2; ocheck env o1; ocheck_binder env (x,o2)
  | O_pt -> ()
  | O_pt_r (o,(x,t)) -> ocheck env o; tcheck_binder (obind (x,nowhere T_Pt) env) (x,t)
  | O_tt -> ()
  | O_coprod (m1,m2,o1,o2) -> ucheck env m1; ucheck env m2; ocheck env o1; ocheck env o2
  | O_ii1 (t,t',o) -> tcheck env t; tcheck env t'; ocheck env o
  | O_ii2 (t,t',o) -> tcheck env t; tcheck env t'; ocheck env o
  | Sum (tT,tT',s,s',o,(x,tS)) -> tcheck env tT; tcheck env tT'; ocheck env s; ocheck env s'; ocheck env o; tcheck_binder env (x,tS)
  | O_empty -> ()
  | O_empty_r (t,o) -> tcheck env t; ocheck env o
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f) -> tcheck env tA; ocheck env a; ttocheck_binder env (x,tB,(y,tD,(z,q))); ocheck env b; ocheck env f
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) 
    -> tcheck env tA; ocheck env a; ttocheck_binder env(x,tB,(y,tD,(z,q))); ocheck env i; t2check_binder env (x',v,tS); ocheck env t
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))) -> ucheck env m1; ucheck env m2; ucheck env m3; ocheck env oA; ocheck env a; ooocheck_binder env (x,oB,(y,oD,(z,q)))
  | O_paths (m,t,x,y) -> ucheck env m; ocheck env t; ocheck env x; ocheck env y
  | O_refl (t,o) -> tcheck env t; ocheck env o
  | O_J (tT,a,b,q,i,(x,e,tS)) -> tcheck env tT; ocheck env a; ocheck env b; ocheck env q; ocheck env i; t2check_binder env (x,e,tS)
  | O_rr0 (m2,m1,s,t,e) -> ucheck env m2; ucheck env m1; ocheck env s; ocheck env t; ocheck env e
  | O_rr1 (m,a,p) -> ucheck env m; ocheck env a; ocheck env p
  | O_def (d,u,t,o) -> List.iter (ucheck env) u; List.iter (tcheck env) t; List.iter (ocheck env) o
and tcheck_binder _ = raise NotImplemented
and ocheck_binder _ = raise NotImplemented
and ttocheck_binder _ = raise NotImplemented
and t2check_binder _ = raise NotImplemented
and ooocheck_binder _ = raise NotImplemented

let ucheck_okay env x = try ucheck env x; true with TypeCheckingFailure _ -> false
let tcheck_okay env x = try tcheck env x; true with TypeCheckingFailure _ -> false
let ocheck_okay env x = try ocheck env x; true with TypeCheckingFailure _ -> false
