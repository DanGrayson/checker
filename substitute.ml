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
  | T_Pt
  | T_Coprod _
  | T_Coprod2 _
  | T_Empty
  | T_IC _
  | Id _
    -> raise NotImplemented
and osubst subs o =
  match o with
    Ovariable v -> (try List.assoc v subs with Not_found -> o)
  | O_u _ -> o
  | O_j _ -> o
  | O_ev(f,p,(v,t)) -> O_ev(osubst subs f,osubst subs p,tsubstfresh subs (v,t))
  | O_lambda (t,(v,p)) -> O_lambda (tsubst subs t,osubstfresh subs (v,p))
  | O_forall (m,m',o,(v,o')) -> O_forall (m,m',osubst subs o,osubstfresh subs (v,o'))
  | O_pair _
  | O_pr1 _
  | O_pr2 _
  | O_total _
  | O_pt
  | O_pt_r _
  | O_tt
  | O_coprod _
  | O_ii1 _
  | O_ii2 _
  | Sum _
  | O_empty
  | O_empty_r _
  | O_c _
  | IC_r _
  | O_ic _
  | O_paths _
  | O_refl _
  | J _
  | O_rr0 _
  | O_rr1 _
    -> raise NotImplemented
