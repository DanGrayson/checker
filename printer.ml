(** Functions for converting expressions to strings for printing *)

open Error
open Variables
open Typesystem
open Names
open Printf

let space x = " " ^ x

let ( <<- ) f g x = f (g x)

let concat = String.concat ""

let concatl = concat <<- List.flatten

let rec remove x = function
  | [] -> []
  | y :: rest -> if x = y then remove x rest else y :: remove x rest

let join a b = List.flatten [a;b]

let pvar free_vars v = if List.mem v free_vars then vartostring v else "_"

(** Printing of LF and TS expressions. 

    In the names of the following routines, "fvs" refers to "free variables and strings".
*)

let rec head_and_args_to_fvs fv p_hd p_arg (h,args) = 
  let r = List.map p_arg args in
  let fv = join (List.flatten (List.map fst r)) fv in
  let args = concat (List.flatten (List.map (fun (_,arg) -> [" ";arg]) r)) in
  let s = concat [p_hd h; args] in
  let s = if String.contains s ' ' then concat ["(";s;")"] else s in
  fv, s

let rec atomic_expr_to_fvs (_,e) : var list * string = 
  match e with
  | TacticHole n -> [], tactic_to_string n
  | EmptyHole n -> [], "?" ^ (string_of_int n)
  | APPLY(V v,[]) -> [v], vartostring v
  | APPLY(h,args) -> 
      let fv = match h with V v -> [v] | _ -> [] in
      head_and_args_to_fvs fv lf_expr_head_to_string lf_expr_to_fvs (h,args)
  | PR1 x -> 
      let (fv,s) = lf_expr_to_fvs x in
      fv, concat ["(π₁ ";s;")"]
  | PR2 x -> 
      let (fv,s) = lf_expr_to_fvs x in
      fv, concat ["(π₂ ";s;")"]

and lf_expr_to_fvs' = function
  | LAMBDA(x,body) -> 
      let (fv,s) = lf_expr_to_fvs' body in
      remove x fv, concat [pvar fv x;" ⟼ ";s]
  | _ as e -> lf_expr_to_fvs e

and lf_expr_to_fvs = function
  | LAMBDA(x,body) -> 
      let (fv,s) = lf_expr_to_fvs' body in
      remove x fv, concat ["(";pvar fv x;" ⟼ ";s;")"]
  | PAIR(_,x,y) -> 
      let (fx,x) = lf_expr_to_fvs x in
      let (fy,y) = lf_expr_to_fvs y in
      join fx fy, concat ["(pair ";x;" ";y;")"]
  | CAN e -> atomic_expr_to_fvs e

let rec dependent_fvs prefix infix target (v,t,u) =
  let (vu,u) = lf_type_to_fvs' true u in
  let used = List.mem v vu in
  let (vt,t) = lf_type_to_fvs' used t in
  let fv = join vt (remove v vu) in
  if used then 
    let k = concat ["("; vartostring v; ":"; t; ")"; infix ; u] in
    fv, if target then k else concat ["("; k; ")"]
  else
    let k = concat [t; infix ; u] in
    fv, if target then k else concat ["("; k; ")"]

and lf_type_to_fvs' target (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_fvs "∏ " " ⟶ " target (v,t,u)
  | F_Sigma(v,t,u) -> dependent_fvs "Σ " " × " target (v,t,u)
  | F_Singleton(x,t) -> 
      let (fx,x) = lf_expr_to_fvs x in
      let (ft,t) = lf_type_to_fvs t in
      join fx ft, concat ["Singleton(";x;" : ";t;")"]
  | F_APPLY(hd,args) -> 
      head_and_args_to_fvs [] lf_type_head_to_string lf_expr_to_fvs (hd,args)

and lf_type_to_fvs t = lf_type_to_fvs' true t

let rec lf_kind_to_fvs = function
  | K_type -> [], "type"
  | K_Pi(v,t,k) -> 
      let prefix = "∏ " in
      let infix = " ⟶ " in
      let (vt,t) = lf_type_to_fvs' false t in
      let (vk,k) = lf_kind_to_fvs k in
      let fv = join vt (remove v vk) in
      if List.mem v vk then 
	fv, concat ["(";prefix; vartostring v; ":"; t; ") "; k]
      else
	fv, concat [t; infix; k]

(** Lists of free variables. *)

let rec vars_args fv p_arg args = 
  let r = List.map p_arg args in
  join (List.flatten r) fv

let rec atomic_expr_to_free_vars (_,e) = 
  match e with
  | TacticHole n -> []
  | EmptyHole n -> []
  | APPLY(V v,[]) -> [v]
  | APPLY(h,args) -> 
      let fv = match h with V v -> [v] | _ -> [] in
      vars_args fv lf_expr_to_vars args
  | PR1 x
  | PR2 x -> lf_expr_to_vars x

and lf_expr_to_vars = function
  | LAMBDA(x,body) -> remove x (lf_expr_to_vars body)
  | PAIR(_,x,y) -> join (lf_expr_to_vars x) (lf_expr_to_vars y)
  | CAN e -> atomic_expr_to_free_vars e

let rec dependent_vars (v,t,u) = join (lf_type_to_vars t) (remove v (lf_type_to_vars u))

and lf_type_to_vars (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_vars (v,t,u)
  | F_Sigma(v,t,u) -> dependent_vars (v,t,u)
  | F_Singleton(x,t) -> join (lf_expr_to_vars x) (lf_type_to_vars t)
  | F_APPLY(hd,args) -> vars_args [] lf_expr_to_vars args

let rec lf_kind_to_vars = function
  | K_type -> []
  | K_Pi(v,t,k) -> join (lf_type_to_vars t) (remove v (lf_kind_to_vars k))

let lf_expr_to_string = snd <<- lf_expr_to_fvs

let atomic_expr_to_string = snd <<- atomic_expr_to_fvs

let lf_type_to_string = snd <<- lf_type_to_fvs

let lf_type_to_string' target = snd <<- (lf_type_to_fvs' target)

let lf_kind_to_string = snd <<- lf_kind_to_fvs

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)

let lf_expr_p e = "$$" ^ (lf_expr_to_string e)

let lf_atomic_p e = "$$" ^ (atomic_expr_to_string e)

let pvar2 free_vars v = if List.mem v free_vars then vartostring v else "_"
let pvar2 free_vars v = vartostring v
let fv = []

let rec args_to_string s = String.concat "," (List.map ts_can_to_string s)

and paren_args_to_string s = String.concat "" [ "("; args_to_string s; ")" ]

and ts_can_to_string = function 
  | CAN e -> ts_expr_to_string e
  | PAIR _ | LAMBDA _ as e -> lf_expr_p e		(* normally this branch will not be used *)

and ts_expr_to_string ((_,e) as oe) = 
  match e with 
  | PR1 _ | PR2 _ -> lf_expr_p (CAN oe)		(* normally this branch will not be used *)
  | TacticHole n -> tactic_to_string n
  | EmptyHole n -> "?" ^ (string_of_int n)
  | APPLY(V v,[]) -> vartostring v
  | APPLY(h,args) -> 
    match h with
    | U uh -> (uhead_to_string uh) ^ (paren_args_to_string args)
    | T th -> (
	match th with 
	| T_Pi -> (
	    match args with
	    | [CAN t1; LAMBDA( x, CAN t2 )] -> 
		if false
		then concat ["(";ts_expr_to_string t1;" ⟶ ";ts_expr_to_string t2;")"]
		else concat ["[∏;";vartostring x;"](";ts_expr_to_string t1;",";ts_expr_to_string t2;")"]
	    | _ -> lf_atomic_p oe)
	| T_Sigma -> (
	    match args with [CAN t1; LAMBDA( x, CAN t2 )] -> "[Sigma;" ^ (pvar2 fv x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
	    | _ -> lf_atomic_p oe)
	| T_Coprod2 -> (
	    match args with 
	    | [CAN t; CAN t'; LAMBDA( x,CAN u); LAMBDA( x', CAN u'); CAN o] ->
		"[Coprod;" ^ (pvar2 fv x) ^ "," ^ (pvar2 fv x') ^ "](" 
		^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		^ (ts_expr_to_string o)
		^ ")"
	    | _ -> lf_atomic_p oe)
	| T_IP -> (
	    match args with 
	      [CAN tA; CAN a;
	       LAMBDA(x1,CAN tB);
	       LAMBDA(x2,LAMBDA(y2,CAN tD));
	       LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,CAN q)))]
	      -> "[IP;" 
		^ (pvar2 fv x1) ^ ","
		^ (pvar2 fv x2) ^ "," ^ (pvar2 fv y2) ^ "," 
		^ (pvar2 fv x3) ^ "," ^ (pvar2 fv y3) ^ "," ^ (pvar2 fv z3) 
		^ "]("
		^ (ts_expr_to_string tA) ^ "," ^ (ts_expr_to_string a) ^ "," ^ (ts_expr_to_string tB) ^ "," ^ (ts_expr_to_string tD) ^ "," ^ (ts_expr_to_string q) ^ ")"
	    | _ -> lf_atomic_p oe)
	| _ -> "[" ^ (thead_to_string th) ^ "]" ^ (paren_args_to_string args)
       )
    | O oh -> (
	match oh with
	| O_ev -> (
	    match args with 
	    | [CAN f;CAN o;LAMBDA(x, CAN t)] ->
		"[ev;" ^ (pvar2 fv x) ^ "](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string t) ^ ")"
	    | [CAN f;CAN o] ->
		"[ev;_](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_lambda -> (
	    match args with 
	    | [CAN t;LAMBDA( x,CAN o)] ->
		"[λ;" (* lambda *) ^ (pvar2 fv x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_forall -> (
	    match args with 
	    | [CAN u;CAN u';CAN o;LAMBDA( x,CAN o')] ->
		"[forall;" ^ (pvar2 fv x) ^ "](" ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string o') ^ ")"
	    | _ -> lf_atomic_p oe)
	| _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (paren_args_to_string args)
       )
    | _ -> (lf_expr_head_to_string h) ^ (paren_args_to_string args)

(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * atomic_expr) list)) 
    -> concatl [
      if List.length uexp_parms > 0 
      then ["(";
	    (String.concat " " (List.map (pvar2 fv) uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ")"]
      else [];
      if List.length texp_parms > 0
      then ["("; 
	    String.concat " " (List.map (pvar2 fv) texp_parms);
	    ":Type)"]
      else [];
      List.flatten (List.map 
		      (fun (v,t) -> ["(";pvar2 fv v; ":"; ts_expr_to_string t;")"])
		      oexp_parms)
    ]

(** Printing of ulevel contexts. *)

let ulevel_context_to_string (UContext(uexp_parms,ueqns)) = 
    concatl [
      if List.length uexp_parms > 0 
      then [
	    (String.concat " " (List.map (pvar2 fv) uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ]
      else [] ]

exception Limit

let rec iteri i f = function
    [] -> ()
  | a::l -> f i a; iteri (i + 1) f l

let iteri f l = iteri 0 f l

(** The following routines can be used with [printf "%a"]. *)

let p_var file x = output_string file (vartostring x)

let phantom s = String.make (String.length s) ' '

let p_var_phantom file x = output_string file (phantom (vartostring x))

let p_ts file x = output_string file (ts_expr_to_string x)

let p_expr file x = output_string file (lf_expr_to_string x)

let p_expr_head file x = output_string file (lf_expr_head_to_string x)

let p_type file x = output_string file (lf_type_to_string x)

let p_type_head file x = output_string file (lf_type_head_to_string x)

let p_kind file x = output_string file (lf_kind_to_string x)

let p_type_head file x = output_string file (lf_type_head_to_string x)

let p_pos file x = output_string file (errfmt x)

let p_pos_of file x = output_string file (errfmt (get_pos x))

let p_fl file () = flush file

let print_signature env file =
  fprintf file "Signature:\n";
  fprintf file "  Type family constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" p_type_head h  p_kind (tfhead_to_kind h)
	    ) lf_type_heads;
  fprintf file "  Object constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" p_expr_head h  p_type (label_to_type env (Error.no_pos 23) h)
	    ) lf_expr_heads;
  flush file

let print_context n file (env:context) = 
  let n = match n with None -> -1 | Some n -> n in
  fprintf file "Context:\n";
  try iteri
      (fun i (v,t) ->
	if i = n then raise Limit;
	match unmark t with
	| F_Singleton(e,t) ->
	    fprintf file "     %a := %a\n" p_var v          p_expr e;
	    fprintf file "     %a  : %a\n" p_var_phantom v  p_type t; flush file
	| _ -> 
	    fprintf file "     %a : %a\n" p_var v  p_type t; flush file
      ) 
      env
  with Limit -> ()

