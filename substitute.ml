open Typesystem

let rec tsubstfresh (subs:oSubs) (v,t) = 
  let v' = fresh v 
  in let subs' = (strip_pos v, with_pos_of v (Ovariable v')) :: subs
  in (with_pos_of v v', tsubst subs' t)
and t2substfresh (subs:oSubs) (v,w,t) = 
  let v' = fresh v and w' = fresh w 
  in let subs' = (strip_pos w, with_pos_of w (Ovariable w')) :: (strip_pos v, with_pos_of v (Ovariable v')) :: subs 
  in (with_pos_of v v', with_pos_of w w', tsubst subs' t)
and osubstfresh subs (v,o) = 
  let v' = fresh v 
  in let subs' = (strip_pos v, with_pos_of v (Ovariable v')) :: subs
  in (with_pos_of v v', osubst subs' o)
and oosubstfresh subs (v,o,k) =
  let v' = fresh v 
  in let subs' = (strip_pos v, with_pos_of v (Ovariable v')) :: subs 
  in (with_pos_of v v', osubst subs' o, osubstfresh subs' k)
and ooosubstfresh subs (v,o,k) = 
  let v' = fresh v 
  in let subs' = (strip_pos v, with_pos_of v (Ovariable v')) :: subs 
  in (with_pos_of v v', osubst subs' o, oosubstfresh subs' k)
and ttosubstfresh subs (v,t,k) = 
  let v' = fresh v 
  in let subs' = (strip_pos v, with_pos_of v (Ovariable v')) :: subs 
  in (with_pos_of v v', tsubst subs t, tosubstfresh subs' k)
and tosubstfresh subs (v,t,k) = 
  let v' = fresh v 
  in let subs' = (strip_pos v, with_pos_of v (Ovariable v')) :: subs 
  in (with_pos_of v v', tsubst subs t, osubstfresh subs' k)
and tsubst subs (pos, t) = with_pos pos (
  match t with
    Tvariable _ -> t
  | TEmptyHole -> t
  | TNumberedEmptyHole _ -> t
  | T_El o -> T_El (osubst subs o)
  | T_U _ -> t
  | T_Pi (t1,(v,t2)) -> T_Pi (tsubst subs t1, tsubstfresh subs (v,t2))
  | T_Sigma (t1,(v,t2)) -> T_Sigma (tsubst subs t1, tsubstfresh subs (v,t2))
  | T_Pt -> t
  | T_Coprod (t,t') -> T_Coprod (tsubst subs t,tsubst subs t')
  | T_Coprod2 (t,t',(x,u),(x',u'),o) -> T_Coprod2 (tsubst subs t,tsubst subs t',tsubstfresh subs (x,u),tsubstfresh subs (x',u'),osubst subs o)
  | T_Empty -> t
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> T_IC (tsubst subs tA,osubst subs a,ttosubstfresh subs (x,tB,(y,tD,(z,q))))
  | Id (t,x,y) -> Id (tsubst subs t,osubst subs x,osubst subs y)
  | T_def (d,u,t,c) -> raise NotImplemented
  | T_nat -> t)
and osubst (subs:oSubs) (pos,o) = with_pos pos (
  match o with
    Ovariable v -> (try strip_pos(List.assoc v subs) with Not_found -> o)
  | OEmptyHole -> o
  | ONumberedEmptyHole _ -> o
  | Onumeral _ -> o 
  | O_u _ -> o
  | O_j _ -> o
  | O_ev(f,p,(v,t)) -> O_ev(osubst subs f,osubst subs p,tsubstfresh subs (v,t))
  | O_lambda (t,(v,p)) -> O_lambda (tsubst subs t,osubstfresh subs (v,p))
  | O_forall (m,m',o,(v,o')) -> O_forall (m,m',osubst subs o,osubstfresh subs (v,o'))
  | O_pair (a,b,(x,t)) -> O_pair (osubst subs a,osubst subs b,tsubstfresh subs (x,t))
  | O_pr1 (t,(x,t'),o) -> O_pr1 (tsubst subs t,tsubstfresh subs (x,t'),osubst subs o)
  | O_pr2 (t,(x,t'),o) -> O_pr2 (tsubst subs t,tsubstfresh subs (x,t'),osubst subs o)
  | O_total (m1,m2,o1,(x,o2)) -> O_total (m1,m2,osubst subs o1,osubstfresh subs (x,o2))
  | O_pt -> o
  | O_pt_r (o,(x,t)) -> O_pt_r (osubst subs o, tsubstfresh subs (x,t))
  | O_tt -> o
  | O_coprod (m1,m2,o1,o2) -> O_coprod (m1,m2,osubst subs o1,osubst subs o2)
  | O_ii1 (t,t',o) -> O_ii1 (tsubst subs t,tsubst subs t',osubst subs o)
  | O_ii2 (t,t',o) -> O_ii2 (tsubst subs t,tsubst subs t',osubst subs o)
  | Sum (tT,tT',s,s',o,(x,tS)) -> Sum (tsubst subs tT,tsubst subs tT',osubst subs s,osubst subs s',osubst subs o,tsubstfresh subs (x,tS))
  | O_empty -> o
  | O_empty_r (t,o) -> O_empty_r (tsubst subs t,osubst subs o)
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f) -> O_c (tsubst subs tA,osubst subs a,ttosubstfresh subs (x,tB,(y,tD,(z,q))),osubst subs b,osubst subs f)
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) 
    -> O_ic_r (tsubst subs tA,osubst subs a,ttosubstfresh subs(x,tB,(y,tD,(z,q))),osubst subs i,t2substfresh subs (x',v,tS),osubst subs t)
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))) -> O_ic (m1,m2,m3,osubst subs oA,osubst subs a,ooosubstfresh subs (x,oB,(y,oD,(z,q))))
  | O_paths (m,t,x,y) -> O_paths (m,osubst subs t,osubst subs x,osubst subs y)
  | O_refl (t,o) -> O_refl (tsubst subs t,osubst subs o)
  | O_J (tT,a,b,q,i,(x,e,tS)) -> O_J (tsubst subs tT,osubst subs a,osubst subs b,osubst subs q,osubst subs i,t2substfresh subs (x,e,tS))
  | O_rr0 (m2,m1,s,t,e) -> O_rr0 (m2,m1,osubst subs s,osubst subs t,osubst subs e)
  | O_rr1 (m,a,p) -> O_rr1 (m,osubst subs a,osubst subs p)
  | O_def (d,u,t,c) -> raise NotImplemented
 )
