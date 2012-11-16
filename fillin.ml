(** In this file, we write a function for filling in the unknown types in an expression, which could not be determined during parsing.
    For example, the third branch of an [ev;_] needs to be filled in, based on the context, using tau.

    This file is not completely implemented: some binders are ignored.
 *)

open Typesystem

let rec tfillin_binder env (v,t) = 
  let env' = env			(* ? *)
  in (v, tfillin env' t)
and t2fillin_binder env (v,w,t) = 
  let env' = env 
  in (v, w, tfillin env' t)
and ofillin_binder env (v,o) = 
  let env' = env in (v, ofillin env' o)
and oofillin_binder env (v,o,k) =
  let env' = env 
  in (v, ofillin env' o, ofillin_binder env' k)
and ooofillin_binder env (v,o,k) = 
  let env' = env 
  in (v, ofillin env' o, oofillin_binder env' k)
and ttofillin_binder env (v,t,k) = 
  let env' = env 
  in (v, tfillin env t, tofillin_binder env' k)
and tofillin_binder env (v,t,k) = 
  let env' = env 
  in (v, tfillin env t, ofillin_binder env' k)
and tfillin env (pos,t) = pos,(
  match t with
    Tvariable _ -> t
  | TEmptyHole | TNumberedEmptyHole _ -> raise (TypingError(pos,"empty t-expression hole, no method for filling"))
  | El o -> El (ofillin env o)
  | T_U _ -> t
  | Pi (t1,(v,t2)) -> Pi (tfillin env t1, tfillin_binder (obind (strip_pos v,t1) env) (v,t2))
  | Sigma (t1,(v,t2)) -> Sigma (tfillin env t1, tfillin_binder (obind (strip_pos v,t1) env) (v,t2))
  | T_Pt -> t
  | T_Coprod (t,t') -> T_Coprod (tfillin env t,tfillin env t')
  | T_Coprod2 (t,t',(x,u),(x',u'),o) -> T_Coprod2 (tfillin env t,tfillin env t',tfillin_binder env (x,u),tfillin_binder env (x',u'),ofillin env o)
  | T_Empty -> t
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> T_IC (tfillin env tA,ofillin env a,ttofillin_binder env (x,tB,(y,tD,(z,q))))
  | Id (t,x,y) -> Id (tfillin env t,ofillin env x,ofillin env y)
  | T_def (d,u,t,o) -> T_def (d,u,List.map (tfillin env) t,List.map (ofillin env) o)
  | T_nat -> t)
and ofillin env ((pos:position),o) = pos,(
  match o with
    Ovariable v -> o
  | Onumeral _ -> o
  | OEmptyHole | ONumberedEmptyHole _ -> raise (TypingError(pos,"empty o-expression hole, no method for filling"))
  | O_u _ -> o
  | O_j _ -> o
  | O_ev(f,p,((_, OVarEmptyHole), (_, TEmptyHole))) -> (
    match strip_pos(Tau.tau env f) with
      | Pi(t1,(x,t2)) -> O_ev(ofillin env f,ofillin env p,tfillin_binder (obind (strip_pos x,t1) env) (x,t2))
      | _ -> raise (TypingError(get_pos f,"expected a product type"))
    )
  | O_ev(f,p,(v,t)) -> O_ev(ofillin env f,ofillin env p,tfillin_binder env (v,t))
  | O_lambda (t,(v,p)) -> O_lambda (tfillin env t,ofillin_binder (obind (strip_pos v,t) env) (v,p))
  | O_forall (m,m',o,(v,o')) -> O_forall (m,m',ofillin env o,ofillin_binder (obind (strip_pos v,nowhere(El o)) env) (v,o'))
  | O_pair (a,b,(x,t)) -> O_pair (ofillin env a,ofillin env b,tfillin_binder env (x,t))
  | O_pr1 (t,(x,t'),o) -> O_pr1 (tfillin env t,tfillin_binder env (x,t'),ofillin env o)
  | O_pr2 (t,(x,t'),o) -> O_pr2 (tfillin env t,tfillin_binder env (x,t'),ofillin env o)
  | O_total (m1,m2,o1,(x,o2)) -> O_total (m1,m2,ofillin env o1,ofillin_binder env (x,o2))
  | O_pt -> o
  | O_pt_r (o,(x,t)) -> O_pt_r (ofillin env o, tfillin_binder (obind (strip_pos x,nowhere T_Pt) env) (x,t))
  | O_tt -> o
  | O_coprod (m1,m2,o1,o2) -> O_coprod (m1,m2,ofillin env o1,ofillin env o2)
  | O_ii1 (t,t',o) -> O_ii1 (tfillin env t,tfillin env t',ofillin env o)
  | O_ii2 (t,t',o) -> O_ii2 (tfillin env t,tfillin env t',ofillin env o)
  | Sum (tT,tT',s,s',o,(x,tS)) -> Sum (tfillin env tT,tfillin env tT',ofillin env s,ofillin env s',ofillin env o,tfillin_binder env (x,tS))
  | O_empty -> o
  | O_empty_r (t,o) -> O_empty_r (tfillin env t,ofillin env o)
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f) -> O_c (tfillin env tA,ofillin env a,ttofillin_binder env (x,tB,(y,tD,(z,q))),ofillin env b,ofillin env f)
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) 
    -> O_ic_r (tfillin env tA,ofillin env a,ttofillin_binder env(x,tB,(y,tD,(z,q))),ofillin env i,t2fillin_binder env (x',v,tS),ofillin env t)
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))) -> O_ic (m1,m2,m3,ofillin env oA,ofillin env a,ooofillin_binder env (x,oB,(y,oD,(z,q))))
  | O_paths (m,t,x,y) -> O_paths (m,ofillin env t,ofillin env x,ofillin env y)
  | O_refl (t,o) -> O_refl (tfillin env t,ofillin env o)
  | O_J (tT,a,b,q,i,(x,e,tS)) -> O_J (tfillin env tT,ofillin env a,ofillin env b,ofillin env q,ofillin env i,t2fillin_binder env (x,e,tS))
  | O_rr0 (m2,m1,s,t,e) -> O_rr0 (m2,m1,ofillin env s,ofillin env t,ofillin env e)
  | O_rr1 (m,a,p) -> O_rr1 (m,ofillin env a,ofillin env p)
  | O_def (d,u,t,o) -> O_def (d,u,List.map (tfillin env) t,List.map (ofillin env) o)
 )
