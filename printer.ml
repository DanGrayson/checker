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
  | ElUU x -> "[UU](" ^ (utostring x) ^ ")"
  | ElForall (t1,(OVar x,t2)) -> "[Pi;" ^ x ^ "](" ^ (ttostring t1) ^ "," ^ (ttostring t2) ^ ")"
  | _ -> "<...>"
and otostring = function
  | Ovariable OVar x -> x
  | Uu x -> "[uu](" ^ (utostring x) ^ ")"
  | _ -> "<...>"
