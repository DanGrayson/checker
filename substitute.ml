open Typesystem

let rec subst subs e = 			(* if subs = (z0,x0) :: (z1,x1) :: ..., then in e substitute z0 for x0, etc.; also written as e[z/x] *)
  match e with 
    ULevel _ -> e
  | Texpr t -> Texpr (tsubst subs t)
  | Oexpr o -> Oexpr (osubst subs o)
and tsubstfresh subs (v,t) = let v' = fresh v in let subs' = (v, Ovariable v') :: subs in (v', tsubst subs' t)
and osubstfresh subs (v,o) = let v' = fresh v in let subs' = (v, Ovariable v') :: subs in (v', osubst subs' o)
and tsubst subs t =
  match t with
    Tvariable _ -> t
  | El o -> El (osubst subs o)
  | UU _ -> t
  | Pi (t1,(v,t2)) -> Pi (tsubst subs t1, tsubstfresh subs (v,t2))
  | Sigma _
  | ElPt
  | ElCoprod _
  | ElCoprod2 _
  | ElEmpty
  | ElIc _
  | ElPaths _
    -> raise NotImplemented
and osubst subs o =
  match o with
    Ovariable v -> (try List.assoc v subs with Not_found -> o)
  | Uu _ -> o
  | Jj _ -> o
  | Ev(f,p,(v,t)) -> Ev(osubst subs f,osubst subs p,tsubstfresh subs (v,t))
  | Lambda (t,(v,p)) -> Lambda (tsubst subs t,osubstfresh subs (v,p))
  | Forall (m,m',o,(v,o')) -> Forall (m,m',osubst subs o,osubstfresh subs (v,o'))
  | Pair _
  | Pr1 _
  | Pr2 _
  | Total _
  | Pt
  | Pt_r _
  | Tt
  | Coprod _
  | Ii1 _
  | Ii2 _
  | Sum _
  | Empty
  | Empty_r _
  | Cc _
  | IC_r _
  | Ic _
  | Paths _
  | Refl _
  | J _
  | Rr0 _
  | Rr1 _
    -> raise NotImplemented
