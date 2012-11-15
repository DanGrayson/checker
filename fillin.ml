(** In this file, we write a function for filling in the unknown types in an expression, which could not be determined during parsing.
    For example, the third branch of an [ev;_] needs to be filled in, based on the context, using tau.

    This file is not completely implemented: some binders are ignored.
 *)

open Typesystem

let rec tfillin_binder ctxt (v,t) = 
  let ctxt' = ctxt
  in (v, tfillin ctxt' t)
and t2fillin_binder ctxt (v,w,t) = 
  let ctxt' = ctxt 
  in (v, w, tfillin ctxt' t)
and ofillin_binder ctxt (v,o) = 
  let ctxt' = ctxt in (v, ofillin ctxt' o)
and oofillin_binder ctxt (v,o,k) =
  let ctxt' = ctxt 
  in (v, ofillin ctxt' o, ofillin_binder ctxt' k)
and ooofillin_binder ctxt (v,o,k) = 
  let ctxt' = ctxt 
  in (v, ofillin ctxt' o, oofillin_binder ctxt' k)
and ttofillin_binder ctxt (v,t,k) = 
  let ctxt' = ctxt 
  in (v, tfillin ctxt t, tofillin_binder ctxt' k)
and tofillin_binder ctxt (v,t,k) = 
  let ctxt' = ctxt 
  in (v, tfillin ctxt t, ofillin_binder ctxt' k)
and tfillin ctxt (t,pos) = nowhere(
  match t with
    Tvariable _ -> t
  | TEmptyHole | TNumberedEmptyHole _ -> raise (TypingError(pos,"empty t-expression hole, no method for filling"))
  | El o -> El (ofillin ctxt o)
  | T_U _ -> t
  | Pi (t1,(v,t2)) -> Pi (tfillin ctxt t1, tfillin_binder ((v,t1) :: ctxt) (v,t2))
  | Sigma (t1,(v,t2)) -> Sigma (tfillin ctxt t1, tfillin_binder ((v,t1) :: ctxt) (v,t2))
  | T_Pt -> t
  | T_Coprod (t,t') -> T_Coprod (tfillin ctxt t,tfillin ctxt t')
  | T_Coprod2 (t,t',(x,u),(x',u'),o) -> T_Coprod2 (tfillin ctxt t,tfillin ctxt t',tfillin_binder ctxt (x,u),tfillin_binder ctxt (x',u'),ofillin ctxt o)
  | T_Empty -> t
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> T_IC (tfillin ctxt tA,ofillin ctxt a,ttofillin_binder ctxt (x,tB,(y,tD,(z,q))))
  | Id (t,x,y) -> Id (tfillin ctxt t,ofillin ctxt x,ofillin ctxt y)
  | T_nat -> t)
and ofillin ctxt (o,pos) = nowhere(
  match o with
    Ovariable v -> o
  | Onumeral _ -> o
  | OEmptyHole | ONumberedEmptyHole _ -> raise (TypingError(pos,"empty o-expression hole, no method for filling"))
  | O_u _ -> o
  | O_j _ -> o
  | O_ev(f,p,(OVarUnused,(TEmptyHole,loc))) -> (
    match strip_pos(Tau.tau ctxt f) with
      | Pi(t1,(x,t2)) -> O_ev(ofillin ctxt f,ofillin ctxt p,tfillin_binder ((x,t1)::ctxt) (x,t2))
      | _ -> raise (TypingError(get_pos f,"expected a product type"))
    )
  | O_ev(f,p,(v,t)) -> O_ev(ofillin ctxt f,ofillin ctxt p,tfillin_binder ctxt (v,t))
  | O_lambda (t,(v,p)) -> O_lambda (tfillin ctxt t,ofillin_binder ((v,t)::ctxt) (v,p))
  | O_forall (m,m',o,(v,o')) -> O_forall (m,m',ofillin ctxt o,ofillin_binder ((v,nowhere(El o))::ctxt) (v,o'))
  | O_pair (a,b,(x,t)) -> O_pair (ofillin ctxt a,ofillin ctxt b,tfillin_binder ctxt (x,t))
  | O_pr1 (t,(x,t'),o) -> O_pr1 (tfillin ctxt t,tfillin_binder ctxt (x,t'),ofillin ctxt o)
  | O_pr2 (t,(x,t'),o) -> O_pr2 (tfillin ctxt t,tfillin_binder ctxt (x,t'),ofillin ctxt o)
  | O_total (m1,m2,o1,(x,o2)) -> O_total (m1,m2,ofillin ctxt o1,ofillin_binder ctxt (x,o2))
  | O_pt -> o
  | O_pt_r (o,(x,t)) -> O_pt_r (ofillin ctxt o, tfillin_binder ((x,nowhere T_Pt)::ctxt) (x,t))
  | O_tt -> o
  | O_coprod (m1,m2,o1,o2) -> O_coprod (m1,m2,ofillin ctxt o1,ofillin ctxt o2)
  | O_ii1 (t,t',o) -> O_ii1 (tfillin ctxt t,tfillin ctxt t',ofillin ctxt o)
  | O_ii2 (t,t',o) -> O_ii2 (tfillin ctxt t,tfillin ctxt t',ofillin ctxt o)
  | Sum (tT,tT',s,s',o,(x,tS)) -> Sum (tfillin ctxt tT,tfillin ctxt tT',ofillin ctxt s,ofillin ctxt s',ofillin ctxt o,tfillin_binder ctxt (x,tS))
  | O_empty -> o
  | O_empty_r (t,o) -> O_empty_r (tfillin ctxt t,ofillin ctxt o)
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f) -> O_c (tfillin ctxt tA,ofillin ctxt a,ttofillin_binder ctxt (x,tB,(y,tD,(z,q))),ofillin ctxt b,ofillin ctxt f)
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) 
    -> O_ic_r (tfillin ctxt tA,ofillin ctxt a,ttofillin_binder ctxt(x,tB,(y,tD,(z,q))),ofillin ctxt i,t2fillin_binder ctxt (x',v,tS),ofillin ctxt t)
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))) -> O_ic (m1,m2,m3,ofillin ctxt oA,ofillin ctxt a,ooofillin_binder ctxt (x,oB,(y,oD,(z,q))))
  | O_paths (m,t,x,y) -> O_paths (m,ofillin ctxt t,ofillin ctxt x,ofillin ctxt y)
  | O_refl (t,o) -> O_refl (tfillin ctxt t,ofillin ctxt o)
  | O_J (tT,a,b,q,i,(x,e,tS)) -> O_J (tfillin ctxt tT,ofillin ctxt a,ofillin ctxt b,ofillin ctxt q,ofillin ctxt i,t2fillin_binder ctxt (x,e,tS))
  | O_rr0 (m2,m1,s,t,e) -> O_rr0 (m2,m1,ofillin ctxt s,ofillin ctxt t,ofillin ctxt e)
  | O_rr1 (m,a,p) -> O_rr1 (m,ofillin ctxt a,ofillin ctxt p))
