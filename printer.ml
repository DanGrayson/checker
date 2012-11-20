(** Functions for converting expressions to strings for printing *)

open Typesystem

let uvartostring' (UVar x) = x
let uvartostring v = uvartostring' (strip_pos_var v)

let tvartostring' (TVar x) = x
let tvartostring v = tvartostring' (strip_pos_var v)

let ovartostring' = function
  | OVar x -> x
  | OVarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | OVarEmptyHole -> "_"
  | OVarUnused -> "_"
let ovartostring v = ovartostring' (strip_pos_var v)

let rec utostring u = match u with
  | UEmptyHole -> "_"
  | UNumberedEmptyHole n -> "_" ^ (string_of_int n)
  | Uvariable x -> uvartostring' x
  | Uplus (x,n) -> "(" ^ (utostring x) ^ "+" ^ (string_of_int n) ^ ")"
  | Umax (x,y) -> "max(" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
  | U_def (d,u) -> "[udef;" ^ d ^ "](" ^ (elisttostring u) ^ ")"
and elisttostring s = String.concat "," (List.map utostring s)

let ueqntostring (u,v) = "; " ^ (utostring u) ^ "=" ^ (utostring v)

let rec etostring = function
  | POS(_,e) -> etostring e
  | UU u -> utostring u
  | TT_variable t -> tvartostring' t
  | OO_variable o -> ovartostring' o
  | Expr(h,args) -> (
      match h with
      | BB x -> "[BIND;" ^ (ovartostring x) ^ "]" ^ (parenelisttostring args)
      | TT th -> (
	  match th with 
	  | TT_EmptyHole -> "_"
	  | TT_NumberedEmptyHole n -> "_" ^ (string_of_int  n)
	  | TT_El -> "[El]" ^ (parenelisttostring args)
	  | TT_U -> "[U]" ^ (parenelisttostring args)
	  | TT_Pi -> (
	      match args with
	      | [t1; Expr( BB x, [t2] )] -> "[Pi;" ^ (ovartostring x) ^ "](" ^ (etostring t1) ^ "," ^ (etostring t2) ^ ")"
	      | _ -> raise InternalError)
	  | TT_Sigma -> (
	      match args with [t1; Expr( BB x, [t2] )] -> "[Sigma;" ^ (ovartostring x) ^ "](" ^ (etostring t1) ^ "," ^ (etostring t2) ^ ")"
	      | _ -> raise InternalError)
	  | TT_Pt -> "[Pt]" ^ (parenelisttostring args)
	  | TT_Coprod -> "[Coprod]" ^ (parenelisttostring args)
	  | TT_Coprod2 -> (
	      match args with 
	      | [t;t'; Expr(BB x,[u]);Expr(BB x', [u']);o] ->
		  "[Coprod;" ^ (ovartostring x) ^ "," ^ (ovartostring x') ^ "](" 
		  ^ (etostring t) ^ "," ^ (etostring t) ^ ","
		  ^ (etostring u) ^ "," ^ (etostring u') ^ ","
		  ^ (etostring o)
		  ^ ")"
	      | _ -> raise InternalError)
	  | TT_Empty -> "[Empty]" ^ (parenelisttostring args)
	  | TT_IC -> (
	      match args with 
		[tA; a; Expr(BB x, [tB;Expr( BB y, [tD;Expr( BB z, [q])])])]
		-> "[IC;" ^ (ovartostring x) ^ "," ^ (ovartostring y) ^ "," ^ (ovartostring z) ^ "]("
		  ^ (etostring tA) ^ "," ^ (etostring a) ^ "," ^ (etostring tB) ^ "," ^ (etostring tD) ^ "," ^ (etostring q) ^ ")"
	      | _ -> raise InternalError)
	  | TT_Id -> "[Id]" ^ (parenelisttostring args)
	  | TT_def_app d -> "[tdef;" ^ d ^ "]" ^ (parenelisttostring args)
	  | TT_nat -> "nat" 
	 )
      | OO oh -> (
	  match oh with
	  | OO_emptyHole -> "_"
	  | OO_numberedEmptyHole n -> "_" ^ (string_of_int  n)
	  | OO_u -> "[u]" ^ (parenelisttostring args)
	  | OO_j -> "[j]" ^ (parenelisttostring args)
	  | OO_ev -> (
	      match args with 
	      | [f;o;Expr(BB x,[t])] ->
		  "[ev;" ^ (ovartostring x) ^ "](" ^ (etostring f) ^ "," ^ (etostring o) ^ "," ^ (etostring t) ^ ")"
	      | _ -> raise InternalError)
	  | OO_lambda -> (
	      match args with 
	      | [t;Expr(BB x,[o])] ->
		  "[lambda;" ^ (ovartostring x) ^ "](" ^ (etostring t) ^ "," ^ (etostring o) ^ ")"
	      | _ -> raise InternalError)
	  | OO_forall -> (
	      match args with 
	      | [u;u';o;Expr(BB x,[o'])] ->
		  "[forall;" ^ (ovartostring x) ^ "](" ^ (etostring u) ^ "," ^ (etostring u') ^ "," ^ (etostring o) ^ "," ^ (etostring o') ^ ")"
	      | _ -> raise InternalError)
	  | OO_def_app d -> "[tdef;" ^ d ^ "]" ^ (parenelisttostring args)
	  | OO_numeral i -> string_of_int i
	  | OO_pair -> "[pair]" ^ (parenelisttostring args)
	  | OO_pr1 -> "[pr1]" ^ (parenelisttostring args)
	  | OO_pr2 -> "[pr2]" ^ (parenelisttostring args)
	  | OO_total -> "[total]" ^ (parenelisttostring args)
	  | OO_pt -> "[pt]" ^ (parenelisttostring args)
	  | OO_pt_r -> "[pt_r]" ^ (parenelisttostring args)
	  | OO_tt -> "[tt]" ^ (parenelisttostring args)
	  | OO_coprod -> "[coprod]" ^ (parenelisttostring args)
	  | OO_ii1 -> "[ii1]" ^ (parenelisttostring args)
	  | OO_ii2 -> "[ii2]" ^ (parenelisttostring args)
	  | OO_sum -> "[sum]" ^ (parenelisttostring args)
	  | OO_empty -> "[empty]()"
	  | OO_empty_r -> "[empty_r]" ^ (parenelisttostring args)
	  | OO_c -> "[c]" ^ (parenelisttostring args)
	  | OO_ic_r -> "[ic_r]" ^ (parenelisttostring args)
	  | OO_ic -> "[ic]" ^ (parenelisttostring args)
	  | OO_paths -> "[paths]" ^ (parenelisttostring args)
	  | OO_refl -> "[refl]" ^ (parenelisttostring args)
	  | OO_J -> "[J]" ^ (parenelisttostring args)
	  | OO_rr0 -> "[rr0]" ^ (parenelisttostring args)
	  | OO_rr1 -> "[rr1]" ^ (parenelisttostring args)
	 )
     )
and elisttostring s = String.concat "," (List.map etostring s)
and parenelisttostring s = String.concat "" [ "("; elisttostring s; ")" ]

let octostring (v,t) = (ovartostring' v) ^ ":" ^ (etostring t)

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
    -> "Define type "         ^n^(parmstostring c)^" := "^(etostring t)^"."
  | ODefinition   (Ident n,(c,o,t   )) ->
      "Define "               ^n^(parmstostring c)^" := "^(etostring o)^" : "^(etostring t)^"."
  | TeqDefinition (Ident n,(c,t,t'  ))
    -> "Define type equality "^n^(parmstostring c)^" := "^(etostring t)^" == "^(etostring t')^"."
  | OeqDefinition (Ident n,(c,o,o',t)) 
    -> "Define equality "     ^n^(parmstostring c)^" := "^(etostring o)^" == "^(etostring o')^" : "^(etostring t)^"."
