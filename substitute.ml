open Typesystem

let rec subst subs e = 			(* if subs = (z0,x0) :: (z1,x1) :: ..., then in e substitute z0 for x0, etc.; also written as e[z/x] *)
  match e with 
    ULevel _ -> e
  | Texpr t -> Texpr (tsubst subs t)
  | Oexpr o -> Oexpr (osubst subs o)
and tsubstfresh subs (v,t) = let v' = fresh v in let subs' = (v, Ovariable v') :: subs in (v', tsubst subs' t)
and t2substfresh subs (v,w,t) = let v' = fresh v and w' = fresh w in let subs' = (w, Ovariable w') :: (v, Ovariable v') :: subs in (v', w', tsubst subs' t)
and osubstfresh subs (v,o) = let v' = fresh v in let subs' = (v, Ovariable v') :: subs in (v', osubst subs' o)
and ttosubstfresh subs (v,t,k) = let v' = fresh v in let subs' = (v, Ovariable v') :: subs in (v', tsubst subs t, tosubstfresh subs' k)
and tosubstfresh subs (v,t,k) = let v' = fresh v in let subs' = (v, Ovariable v') :: subs in (v', tsubst subs t, osubstfresh subs' k)
and tsubst subs t =
  match t with
    Tvariable _ -> t
  | El o -> El (osubst subs o)
  | UU _ -> t
  | Pi (t1,(v,t2)) -> Pi (tsubst subs t1, tsubstfresh subs (v,t2))
  | Sigma (t1,(v,t2)) -> Sigma (tsubst subs t1, tsubstfresh subs (v,t2))
  | T_Pt -> t
  | T_Coprod (t,t') -> T_Coprod (tsubst subs t,tsubst subs t')
  | T_Coprod2 (t,t',(x,u),(x',u'),o) -> T_Coprod2 (tsubst subs t,tsubst subs t',tsubstfresh subs (x,u),tsubstfresh subs (x',u'),osubst subs o)
  | T_Empty -> t
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))) -> T_IC (tsubst subs tA,osubst subs a,ttosubstfresh subs (x,tB,(y,tD,(z,q))))
  | Id (t,x,y) -> Id (tsubst subs t,osubst subs x,osubst subs y)
and osubst subs o =
  match o with
    Ovariable v -> (try List.assoc v subs with Not_found -> o)
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
  | IC_r (tA,a,(x,tB,(y,tD,(z,q))),i,(x',v,tS),t) 
    -> IC_r (tsubst subs tA,osubst subs a,ttosubstfresh subs(x,tB,(y,tD,(z,q))),osubst subs i,t2substfresh subs (x',v,tS),osubst subs t)
  | O_ic _
  | O_paths _
  | O_refl _
  | J _
  | O_rr0 _
  | O_rr1 _
    -> raise NotImplemented
