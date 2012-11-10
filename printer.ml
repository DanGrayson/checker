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
  | ElUU x -> "[U](" ^ (utostring x) ^ ")"
  | ElForall (t1,(OVar x,t2)) -> "[Pi;" ^ x ^ "](" ^ (ttostring t1) ^ "," ^ (ttostring t2) ^ ")"
  | _ -> "<...>"
and otostring = function
  | Ovariable OVar x -> x
  | Uu x -> "[u](" ^ (utostring x) ^ ")"
  | Jj (x,y) -> "[j](" ^ (utostring x) ^ "," ^ (utostring x) ^ ")"
  | Ev (f,o,(OVar x,t)) -> "[ev;" ^ x ^ "](" ^ (otostring f) ^ "," ^ (otostring o) ^ "," ^ (ttostring t) ^ ")"
  | Lambda (t,(OVar x,o)) -> "[lambda;" ^ x ^ "](" ^ (ttostring t) ^ "," ^ (otostring o) ^ ")"
  | _ -> "<...>"
