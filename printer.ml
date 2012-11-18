(** Functions for converting expressions to strings for printing *)

open Typesystem

let ovartostring' = function
  | OVar x -> x
  | OVarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | OVarEmptyHole -> "_"
  | OVarUnused -> "_"
let ovartostring v = ovartostring' (strip_pos v)

let uvartostring' (UVar x) = x
let uvartostring v = uvartostring' (strip_pos v)

let rec utostring u = match strip_pos u with
  | UEmptyHole -> "_"
  | UNumberedEmptyHole n -> "_" ^ (string_of_int n)
  | Uvariable x -> uvartostring' x
  | Uplus (x,n) -> "(" ^ (utostring x) ^ "+" ^ (string_of_int n) ^ ")"
  | Umax (x,y) -> "max(" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
  | U_def (d,u) -> "[udef;" ^ d ^ "](" ^ (ulisttostring u) ^ ")"
and ulisttostring s = String.concat "," (List.map utostring s)

let ueqntostring (u,v) = "; " ^ (utostring u) ^ "=" ^ (utostring v)

let tvartostring' (TVar x) = x
let tvartostring v = tvartostring' (strip_pos v)

let rec ttostring = function
  | (_,t) -> ttostring' t
and ttostring' = function
  | T_EmptyHole -> "_"
  | T_NumberedEmptyHole n -> "_" ^ (string_of_int  n)
  | T_variable x -> tvartostring' x
  | T_El x -> "[El](" ^ (otostring x) ^ ")"
  | T_U x -> "[U](" ^ (utostring x) ^ ")"
  | T_Pi (t1,(x,t2)) -> "[Pi;" ^ (ovartostring x) ^ "](" ^ (ttostring t1) ^ "," ^ (ttostring t2) ^ ")"
  | T_Sigma (t,(x,t')) -> "[Sigma;" ^ (ovartostring x) ^ "](" ^ (ttostring t) ^ "," ^ (ttostring t') ^ ")"
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
  | T_Id (t,x,y) -> "[Id](" ^ (ttostring t) ^ "," ^ (otostring x) ^ "," ^ (otostring y) ^ ")"
  | T_def (d,u,t,o) -> "[tdef;" ^ d ^ "](" ^ (ulisttostring u) ^ ";" ^ (tlisttostring t) ^ ";" ^ (olisttostring o) ^ ")"
  | T_nat -> "nat"
and otostring = function
  | (_,o) -> otostring' o
and otostring' = function
  | O_emptyHole -> "_"
  | O_numberedEmptyHole n -> "_" ^ (string_of_int  n)
  | O_variable x -> ovartostring' x
  | O_u x -> "[u](" ^ (utostring x) ^ ")"
  | O_j (x,y) -> "[j](" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
  | O_ev (f,o,(x,t)) -> "[ev;" ^ (ovartostring x) ^ "](" ^ (otostring f) ^ "," ^ (otostring o) ^ "," ^ (ttostring t) ^ ")"
  | O_lambda (t,(x,o)) -> "[lambda;" ^ (ovartostring x) ^ "](" ^ (ttostring t) ^ "," ^ (otostring o) ^ ")"
  | O_forall (u,u',o,(x,o')) -> "[forall;" ^ (ovartostring x) ^ "](" ^ (utostring u) ^ "," ^ (utostring u') ^ "," ^ (otostring o) ^ "," ^ (otostring o') ^ ")"
  | O_def (d,u,t,o) -> "[odef;" ^ d ^ "](" ^ (ulisttostring u) ^ ";" ^ (tlisttostring t) ^ ";" ^ (olisttostring o) ^ ")"
  | O_numeral i -> string_of_int i
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
  | O_sum _ -> raise NotImplemented
  | O_empty -> "[empty]()"
  | O_empty_r (t,o) -> "[empty_r](" ^ (ttostring t) ^ "," ^ (otostring o) ^ ")"
  | O_c _
  | O_ic_r _
  | O_ic _
  | O_paths _
  | O_refl _
  | O_J _
  | O_rr0 _
  | O_rr1 _ -> raise NotImplemented
and tlisttostring s = String.concat "," (List.map ttostring s)
and olisttostring s = String.concat "," (List.map otostring s)

let octostring (v,t) = (ovartostring' v) ^ ":" ^ (ttostring t)

let parmstostring = function
  | ((UContext(uvars,ueqns):uContext),(tc:tContext),(oc:oContext)) 
    -> (
      if List.length uvars > 0 
      then "(" ^ (String.concat " " (List.map uvartostring' uvars)) ^ ":Univ" ^ (String.concat "" (List.map ueqntostring ueqns)) ^ ")"
      else "" )
      ^ 
	(
	 if List.length tc > 0
	 then "(" ^ (String.concat " " (List.map tvartostring' tc)) ^ ":Type)"
	 else ""
	) ^
      (String.concat "" (List.map (fun x -> "(" ^ (octostring x) ^ ")") oc))
	
let definitiontostring = function
  | TDefinition   (Ident n,(c,  t   ))
    -> "Define type "         ^n^(parmstostring c)^" := "^(ttostring t)^"."
  | ODefinition   (Ident n,(c,o,t   )) ->
      "Define "               ^n^(parmstostring c)^" := "^(otostring o)^" : "^(ttostring t)^"."
  | TeqDefinition (Ident n,(c,t,t'  ))
    -> "Define type equality "^n^(parmstostring c)^" := "^(ttostring t)^" == "^(ttostring t')^"."
  | OeqDefinition (Ident n,(c,o,o',t)) 
    -> "Define equality "     ^n^(parmstostring c)^" := "^(otostring o)^" == "^(otostring o')^" : "^(ttostring t)^"."
