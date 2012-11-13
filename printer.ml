open Typesystem

let ovartostring = function
  | OVar x -> x
  | OVarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | OVarDummy -> "_"

let uvartostring = function
  | UVar x -> x
let rec utostring = function
  | Unumeral i -> string_of_int i
  | Uvariable x -> uvartostring x
  | Uplus (x,n) -> "(" ^ (utostring x) ^ "+" ^ (string_of_int n) ^ ")"
  | Umax (x,y) -> "max(" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
let ueqntostring (u,v) = ";" ^ (utostring u) ^ "=" ^ (utostring v)

let tvartostring = function
  | TVar x -> x
  | TVarDummy -> "__Unknown_type__"

let rec ttostring = function
  | Tvariable x -> tvartostring x
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

let jtostring = function
  | EmptyJ _ -> "context judgement"
  | TypeJ _ -> "type judgement"
  | TypeEqJ _ -> "type equality judgement"
  | ObjEqJ _ -> "object equality judgement"

let octostring (v,t) = (ovartostring v) ^ ":" ^ (ttostring t)

let parmstostring = function
  | Context(UContext(uvars,ueqns),tc,oc) 
    ->
      "(" ^ (String.concat "," (List.map uvartostring uvars)) ^ ":ulevel"^
      (String.concat "" (List.map ueqntostring ueqns)) ^
      ")"^
      "(" ^ (String.concat "," (List.map tvartostring tc)) ^ ":Type)"^
      "(" ^ (String.concat "," (List.map octostring oc)) ^ ")"

let deftostring = function
  | TDefinition (Ident name,c,t) -> "t-Definition "^name^(parmstostring c)^" := "^(ttostring t)^"."
  | ODefinition (Ident name,c,o,t) -> "o-Definition "^name^(parmstostring c)^" := "^(otostring o)^" : "^(ttostring t)^"."
