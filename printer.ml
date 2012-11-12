open Typesystem
let rec tostring = function
  | ULevel x -> utostring x
  | Texpr x -> ttostring x
  | Oexpr x -> otostring x
and utostring = function
  | Unumeral i -> string_of_int i
  | Uvariable UVar x -> x
  | Uplus (x,n) -> "(" ^ (utostring x) ^ "+" ^ (string_of_int n) ^ ")"
  | Umax (x,y) -> "max(" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
and ttostring = function
  | Tvariable TVar x -> x
  | El x -> "[El](" ^ (otostring x) ^ ")"
  | T_U x -> "[U](" ^ (utostring x) ^ ")"
  | Pi (t1,(x,t2)) -> "[Pi;" ^ (ovartostring x) ^ "](" ^ (ttostring t1) ^ "," ^ (ttostring t2) ^ ")"
  | Sigma (t,(x,t')) -> "[Sigma;" ^ (ovartostring x) ^ "](" ^ (ttostring t) ^ "," ^ (ttostring t') ^ ")"
  | T_Pt -> "[Pt]()"
  | T_Coprod (t,t') -> "[Coprod](" ^ (ttostring t) ^ "," ^ (ttostring t) ^ ")"
  | T_Coprod2 (t,t',(x,u),(x',u'),o) 
    -> "[Coprod;" ^ (ovartostring x) ^ "," ^ (ovartostring x') ^ "](" 
      ^ (ttostring t) ^ "," ^ (ttostring t) ^ ","
      ^ (ttostring u) ^ "," ^ (ttostring u') ^ ","
      ^ (otostring o)
      ^ ")"
  | T_Empty -> "[Empty]()"
  | T_IC (tA,a,(x,tB,(y,tD,(z,q))))
    -> "[IC;" ^ (ovartostring x) ^ "," ^ (ovartostring y) ^ "," ^ (ovartostring z) ^ "]("
      ^ (ttostring tA) ^ "," ^ (otostring a) ^ "," ^ (ttostring tB) ^ "," ^ (ttostring tD) ^ "," ^ (otostring q) ^ ")"
  | Id (t,x,y) -> "[Id](" ^ (ttostring t) ^ "," ^ (otostring x) ^ "," ^ (otostring y) ^ ")"
and otostring = function
  | Ovariable x -> ovartostring x
  | O_u x -> "[u](" ^ (utostring x) ^ ")"
  | O_j (x,y) -> "[j](" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
  | O_ev (f,o,(x,t)) -> "[ev;" ^ (ovartostring x) ^ "](" ^ (otostring f) ^ "," ^ (otostring o) ^ "," ^ (ttostring t) ^ ")"
  | O_lambda (t,(x,o)) -> "[lambda;" ^ (ovartostring x) ^ "](" ^ (ttostring t) ^ "," ^ (otostring o) ^ ")"
  | O_forall (u,u',o,(x,o')) -> "[forall;" ^ (ovartostring x) ^ "](" ^ (utostring u) ^ "," ^ (utostring u') ^ "," ^ (otostring o) ^ "," ^ (otostring o') ^ ")"
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
  | O_ic_r _
  | O_ic _
  | O_paths _
  | O_refl _
  | O_J _
  | O_rr0 _
  | O_rr1 _
     -> "<...>"
and ovartostring = function
  | OVar x -> x
  | OVarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | OVarDummy -> "_"
