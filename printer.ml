open Typesystem
let rec tostring = function
  | ULevel x -> utostring x
  | Texpr x -> ttostring x
  | Oexpr x -> otostring x
and utostring = function
  | Uvariable UVar x -> x
  | Uplus (x,n) -> "(" ^ (utostring x) ^ "+" ^ (string_of_int n) ^ ")"
  | Umax (x,y) -> "max(" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
and ttostring = function
  | Tvariable TVar x -> x
  | El x -> "[El](" ^ (otostring x) ^ ")"
  | UU x -> "[U](" ^ (utostring x) ^ ")"
  | ElForall (t1,(x,t2)) -> "[Pi;" ^ (ovartostring x) ^ "](" ^ (ttostring t1) ^ "," ^ (ttostring t2) ^ ")"
  | ElTotal _
  | ElPt
  | ElCoprod _
  | ElCoprod2 _
  | ElEmpty
  | ElIc _
  | ElPaths _
    -> raise NotImplemented
and otostring = function
  | Ovariable x -> ovartostring x
  | Uu x -> "[u](" ^ (utostring x) ^ ")"
  | Jj (x,y) -> "[j](" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
  | Ev (f,o,(x,t)) -> "[ev;" ^ (ovartostring x) ^ "](" ^ (otostring f) ^ "," ^ (otostring o) ^ "," ^ (ttostring t) ^ ")"
  | Lambda (t,(x,o)) -> "[lambda;" ^ (ovartostring x) ^ "](" ^ (ttostring t) ^ "," ^ (otostring o) ^ ")"
  | Forall (u,u',o,(x,o')) -> "[forall;" ^ (ovartostring x) ^ "](" ^ (utostring u) ^ "," ^ (utostring u') ^ "," ^ (otostring o) ^ "," ^ (otostring o') ^ ")"
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
     -> "<...>"
and ovartostring = function
  | OVar x -> x
  | OVarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | OVarDummy -> "_"
