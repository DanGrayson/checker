open Typesystem

let rec subst subs e = 			(* if subs = (z0,x0) :: (z1,x1) :: ..., then in e substitute z0 for x0, etc.; also written as e[z/x] *)
  match e with 
    ULevel _ -> e
  | Texpr t -> Texpr (tsubst subs t)
  | Oexpr o -> Oexpr (osubst subs o)
and tsubst subs t =
  match t with
    Tvariable _ -> t
  | El o -> El (osubst subs o)
  | ElUU _ -> t
  | ElForall (t1,(OVar v,t2)) -> 
      let v' = fresh v in
      ElForall (tsubst subs t1, (v', tsubst ((v, v') :: subs) t2))
  | _ -> t
and osubst subs o =
  match o with
    Ovariable OVar v -> Ovariable (try List.assoc v subs with Not_found -> OVar v)
  | _ -> o

