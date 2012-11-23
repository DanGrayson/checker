(** Functions for converting expressions to strings for printing *)

open Typesystem

let rec utostring = function
  | Upos (_,u) -> utostring u
  | UEmptyHole -> "_"
  | UNumberedEmptyHole n -> "_" ^ (string_of_int n)
  | Uvariable x -> vartostring' x
  | Uplus (x,n) -> "(" ^ (utostring x) ^ "+" ^ (string_of_int n) ^ ")"
  | Umax (x,y) -> "max(" ^ (utostring x) ^ "," ^ (utostring y) ^ ")"
  | U_def (d,u) -> "[udef;" ^ d ^ "](" ^ (elisttostring u) ^ ")"
and elisttostring s = String.concat "," (List.map utostring s)

let ueqntostring (u,v) = "; " ^ (utostring u) ^ "=" ^ (utostring v)

let rec etostring = function
  | LAMBDA(x,bodies) -> raise Error.NotImplemented
  | POS(_,e) -> match e with 
    | UU u -> utostring u
    | Variable v -> vartostring' v
    | APPLY(h,args) -> (
	match h with
	| TT th -> (
	    match th with 
	    | TT_Pi -> (
		match args with
		| [t1; LAMBDA( x, [t2] )] -> "[Pi;" ^ (vartostring x) ^ "](" ^ (etostring t1) ^ "," ^ (etostring t2) ^ ")"
		| _ -> raise Error.Internal)
	    | TT_Sigma -> (
		match args with [t1; LAMBDA( x, [t2] )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (etostring t1) ^ "," ^ (etostring t2) ^ ")"
		| _ -> raise Error.Internal)
	    | TT_Coprod2 -> (
		match args with 
		| [t;t'; LAMBDA( x,[u]);LAMBDA( x', [u']);o] ->
		    "[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		    ^ (etostring t) ^ "," ^ (etostring t) ^ ","
		    ^ (etostring u) ^ "," ^ (etostring u') ^ ","
		    ^ (etostring o)
		    ^ ")"
		| _ -> raise Error.Internal)
	    | TT_IC -> (
		match args with 
		  [tA; a; LAMBDA( x, [tB;LAMBDA( y, [tD;LAMBDA( z, [q])])])]
		  -> "[IC;" ^ (vartostring x) ^ "," ^ (vartostring y) ^ "," ^ (vartostring z) ^ "]("
		    ^ (etostring tA) ^ "," ^ (etostring a) ^ "," ^ (etostring tB) ^ "," ^ (etostring tD) ^ "," ^ (etostring q) ^ ")"
		| _ -> raise Error.Internal)
	    | _ -> "[" ^ (thead_to_string th) ^ "]" ^ (parenelisttostring args)
	   )
	| OO oh -> (
	    match oh with
	    | OO_ev -> (
		match args with 
		| [f;o;LAMBDA( x,[t])] ->
		    "[ev;" ^ (vartostring x) ^ "](" ^ (etostring f) ^ "," ^ (etostring o) ^ "," ^ (etostring t) ^ ")"
		| [f;o] ->
		    "[ev;_](" ^ (etostring f) ^ "," ^ (etostring o)
		| _ -> raise Error.Internal)
	    | OO_lambda -> (
		match args with 
		| [t;LAMBDA( x,[o])] ->
		    "[lambda;" ^ (vartostring x) ^ "](" ^ (etostring t) ^ "," ^ (etostring o) ^ ")"
		| _ -> raise Error.Internal)
	    | OO_forall -> (
		match args with 
		| [u;u';o;LAMBDA( x,[o'])] ->
		    "[forall;" ^ (vartostring x) ^ "](" ^ (etostring u) ^ "," ^ (etostring u') ^ "," ^ (etostring o) ^ "," ^ (etostring o') ^ ")"
		| _ -> raise Error.Internal)
	    | _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (parenelisttostring args)
	   )
       )
and elisttostring s = String.concat "," (List.map etostring s)
and parenelisttostring s = String.concat "" [ "("; elisttostring s; ")" ]

let octostring (v,t) = (vartostring' v) ^ ":" ^ (etostring t)

let parmstostring = function
  | ((UContext(uvars,ueqns):uContext),(tc:tContext),(oc:oContext)) 
    -> (
      if List.length uvars > 0 
      then "(" ^ (String.concat " " (List.map vartostring' uvars)) ^ ":Univ" ^ (String.concat "" (List.map ueqntostring ueqns)) ^ ")"
      else "" )
      ^ 
	(
	 if List.length tc > 0
	 then "(" ^ (String.concat " " (List.map vartostring' tc)) ^ ":Type)"
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

let rec lfl label s = "(" ^ label ^ (String.concat "" (List.map (fun x -> " " ^ (lftostring x)) s)) ^ ")"
and lftostring = function
  | LAMBDA(x,bodies) -> "(LAMBDA " ^ (vartostring x) ^ " : Obj" ^ (String.concat "" (List.map (fun x -> ", " ^ (lftostring x)) bodies)) ^ ")"
  | POS(_,e) -> match e with 
    | UU u -> utostring u
    | Variable v -> vartostring' v
    | APPLY(h,args) -> lfl (head_to_string h) args

