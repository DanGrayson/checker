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
  | _ -> "<...>"
and otostring = function
  | Ovariable OVar x -> x
  | _ -> "<...>"
