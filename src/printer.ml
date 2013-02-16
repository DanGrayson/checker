(** Functions for converting expressions to strings for printing *)

let enable_variable_prettification = true

open Error
open Variables
open Helpers
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

let pvar free_vars v = if List.mem v free_vars then vartostring v else "_"

(** Lists of free variables. *)

let rec vars_in_list p_arg args = List.flatten (List.map p_arg args)

let rec vars_in_spine args = 
  match args with 
  | ARG(x,args) -> lf_expr_to_vars x @ vars_in_spine args
  | CAR args | CDR args -> vars_in_spine args
  | END -> []

and head_to_vars h = 
  match h with
  | V v -> [v]
  | FUN(f,t) -> lf_expr_to_vars f @ lf_type_to_vars t
  | U _ | T _ | W _ | O _ | TAC _ -> []

and lf_expr_to_vars (pos,e) = match e with
  | LAMBDA(x,body) -> remove x (lf_expr_to_vars body)
  | CONS(x,y) -> lf_expr_to_vars x @ lf_expr_to_vars y
  | APPLY(V v,END) -> [v]
  | APPLY(h,args) -> head_to_vars h @ vars_in_spine args

and dependent_vars (v,t,u) = lf_type_to_vars t @ remove v (lf_type_to_vars u)

and lf_type_to_vars (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_vars (v,t,u)
  | F_Sigma(v,t,u) -> dependent_vars (v,t,u)
  | F_Singleton(x,t) -> lf_expr_to_vars x @ lf_type_to_vars t
  | F_Apply(hd,args) -> vars_in_list lf_expr_to_vars args

let rec lf_kind_to_vars = function
  | K_primitive_judgment | K_ulevel | K_expression | K_witnessed_judgment | K_judgment | K_judged_expression -> []
  | K_Pi(v,t,k) -> lf_type_to_vars t @ remove v (lf_kind_to_vars k)

(** Whether [x] occurs as a free variable in an expression. *)

let rec occurs_in_head w h =
  match h with 
  | V v -> w = v
  | FUN(f,t) -> occurs_in_expr w f || occurs_in_type w t
  | W _ | U _ | T _ | O _ | TAC _ -> false

and occurs_in_expr w e = 
  match unmark e with 
  | LAMBDA(v,body) -> w <> v && occurs_in_expr w body
  | CONS(x,y) -> occurs_in_expr w x || occurs_in_expr w y
  | APPLY(h,  args) -> occurs_in_head w h || exists_in_spine (occurs_in_expr w) args

and occurs_in_type w (_,t) = match t with
  | F_Pi   (v,t,u)
  | F_Sigma(v,t,u) -> occurs_in_type w t || w <> v && occurs_in_type w u
  | F_Singleton(e,t) -> occurs_in_expr w e || occurs_in_type w t
  | F_Apply(h,args) -> List.exists (occurs_in_expr w) args

let rec occurs_in_kind w = function
  | K_primitive_judgment | K_ulevel | K_expression | K_witnessed_judgment | K_judgment | K_judged_expression -> false
  | K_Pi(v,t,k) -> occurs_in_type w t || w <> v && occurs_in_kind w k

(** Printing of LF and TS expressions. 

    In the names of the following routines, "fvs" refers to "free variables and strings".
*)

(*
  Example of pretty printing of variables:

  x$111 |-> ... x$111 ... x$222 ... x2 ...

  Can't make it pretty in one pass

  Maintain a list of variable substitutions, e.g., x$222 => x, x$333 => x0, ...

  Refer to the list whenever printing a variable

  Replace x$111 by x555 where 555 is the smallest number (or empty) so that x555 is not in the target of the list
  and also not free in the body

  Then  

      x$222 |-> x$111 |-> ... x$111 ... x$222 ... x2 ...

  will print as

      x |-> x1 |-> ... x1 ... x ... x2 ...

 *)

let var_sub subs v = try List.assoc v subs with Not_found -> v

let in_range w subs = List.exists (fun (_,v) -> v = w) subs

let var_tester w subs occurs_in e =
  not( in_range w subs )
    &&
  not( occurs_in w e )

let var_chooser x subs occurs_in e =
  if not enable_variable_prettification then x, subs else
  match x with
  | Var_wd name | VarGen_wd(_,name) -> 
      if not (occurs_in x e) then Var_wd "_", subs else
      let w = Var_wd name in
      if x = w && not( in_range w subs ) || var_tester w subs occurs_in e then w, (x,w) :: subs
      else let rec repeat i =
        let w = Var_wd (name ^ (if i = 0 then "'" else string_of_int i)) in
        if var_tester w subs occurs_in e then w, (x,w) :: subs
        else repeat (i+1)
      in repeat 1			(*omit the "'" case*)
  | Var name | VarGen(_,name) -> 
      if not (occurs_in x e) then Var "_", subs else
      let w = Var name in
      if x = w && not( in_range w subs ) || var_tester w subs occurs_in e then w, (x,w) :: subs
      else let rec repeat i =
        let w = Var (name ^ (if i = 0 then "'" else string_of_int i)) in
        if var_tester w subs occurs_in e then w, (x,w) :: subs
        else repeat (i+1)
      in repeat 1			(*omit the "'" case*)

let occurs_in_list occurs_in x args = List.exists (occurs_in x) args

(* these precedences mirror those in grammar.mly: *)
type associativity = RIGHT | LEFT | NONASSOC
let assoc_to_string = function RIGHT -> "RIGHT" | LEFT -> "LEFT" | NONASSOC -> "NONASSOC"
type precedence = int * associativity
let prec_to_string (i,a) = "(" ^ string_of_int i ^ "," ^ assoc_to_string a ^ ")"
type smart_string = precedence * string
let bottom_prec = 0,NONASSOC
let colon_prec = 10,NONASSOC
let comma_prec = 20,NONASSOC
let binder_prec = 30,RIGHT
let arrow_prec = 40,RIGHT
let times_prec = arrow_prec
let spine_prec = 50,LEFT
let star_prec = 60,NONASSOC
let slash_prec = 80,LEFT
let start_prec = 90,NONASSOC
let apply_prec = 100,NONASSOC
let list_prec = 110,LEFT
let top_level = 200
let subscript_prec = top_level,LEFT
let top_prec = top_level,NONASSOC

    (* 

       We still need to arrange for all the parentheses in expressions like these:

	   ([ev] f o (_ |-> U))

	   ([ev] f ([ev] g t _) _)

	   _ |-> ([ev] g t _)

       and none here:

	   _ |-> _ |-> T

     *)


type choice = REDUCE | SHIFT | NEITHER

let choose (production:precedence) (token:precedence) =
  (* this algorithm mirrors the behavior of yacc and menhir *)
  let (p,_) = production in
  let (t,a) = token in
  if p > t then REDUCE else
  if p < t then SHIFT else
    match a with
    | RIGHT -> SHIFT
    | LEFT -> REDUCE
    | NONASSOC -> NEITHER

(* to decide whether to parenthesize while printing something like

       a op1 b     op     c op2 d

    where op1,op,op2 have precedences p1,p,p2:

   choose p1 p = SHIFT       (a op1 b)
   choose p1 p = REDUCE       a op1 b
   choose p1 p = NEITHER     (a op1 b)
   
   choose p p2 = SHIFT        c op2 d
   choose p p2 = REDUCE      (c op2 d)
   choose p p2 = NEITHER     (c op2 d)

*)

let paren_left p (p1,s) = if choose p1 p = REDUCE then s else "(" ^ s ^ ")"

let paren_right p (p2,s) = if choose p p2 = SHIFT then s else "(" ^ s ^ ")"

let paren_always (p,s) = "(" ^ s ^ ")"

let paren_never (p,s) = s

let mark_top s = top_prec, s

let make_top ((i,a),s) = top_prec, if i = top_level then s else "(" ^ s ^ ")"

let rec list_application_to_string p_hd p_arg (head,args) : smart_string = 
  List.fold_left
    (fun accu arg -> list_prec, paren_left list_prec accu ^ " " ^ paren_right list_prec (p_arg arg))
    (p_hd head) args

let p1 k = subscript_prec, paren_left subscript_prec k ^ "₁"

let p2 k = subscript_prec, paren_left subscript_prec k ^ "₂"

let application_to_lf_string p_arg head args : smart_string =
  make_top (
  args_fold 
    (fun accu arg -> spine_prec, paren_left spine_prec accu ^ " " ^ paren_right spine_prec (p_arg arg))
    p1 p2
    head args)

let rec lf_head_to_string_with_subs subs h : string =
  match h with
  | V v -> vartostring (var_sub subs v)
  | W _ | U _ | T _ | O _ -> "@[" ^ expr_head_to_string h ^ "]"
  | TAC tac -> tactic_to_string tac
  | FUN(f,t) ->
      let f = lf_expr_to_string_with_subs subs f in
      let t = lf_type_to_string_with_subs subs t in
      concat["("; paren_left colon_prec f; " : "; paren_right colon_prec t; ")"]

and lf_expr_to_string_with_subs subs e : smart_string = 
  match unmark e with
  | LAMBDA(x,body) -> 
      let w,subs = var_chooser x subs occurs_in_expr body in
      let s = lf_expr_to_string_with_subs subs body in
      arrow_prec, concat [vartostring (var_sub subs w);" ⟼ ";paren_right arrow_prec s]
  | CONS(x,y) -> 
      let x = lf_expr_to_string_with_subs subs x in
      let y = lf_expr_to_string_with_subs subs y in
      (* printf " printing pair: prec x = %s, prec y = %s\n\t x = %s\n\t y = %s\n%!" (prec_to_string (fst x)) (prec_to_string (fst y)) (snd x) (snd y); *)
      top_prec, concat ["(pair ";paren_left list_prec x;" ";paren_left list_prec y;")"]
  | APPLY(h,args) -> 
      let h = top_prec, lf_head_to_string_with_subs subs h in
      application_to_lf_string (lf_expr_to_string_with_subs subs) h args

and dependent_sub subs prefix infix infix_prec (v,t,u) =
  let used = not enable_variable_prettification || occurs_in_type v u in
  let w,subs = var_chooser v subs occurs_in_type u in
  let u = lf_type_to_string_with_subs subs u in
  let t = lf_type_to_string_with_subs subs t in
  infix_prec, 
  (
   if used then 
     concat ["("; vartostring w; ":"; paren_right colon_prec t; ")"]
   else
     paren_left infix_prec t
  ) 
  ^ infix 
  ^ paren_right infix_prec u

and lf_type_to_string_with_subs subs (_,t) : smart_string = match t with
  | F_Pi   (v,t,u) -> dependent_sub subs "∏ " " ⟶ " arrow_prec (v,t,u)
  | F_Sigma(v,t,u) -> dependent_sub subs "Σ " " × " times_prec (v,t,u)
  | F_Singleton(x,t) -> 
      let x = lf_expr_to_string_with_subs subs x in
      let t = lf_type_to_string_with_subs subs t in
      top_prec, concat ["Singleton(";paren_left colon_prec x;" : ";paren_right colon_prec t;")"]
  | F_Apply(hd,args) -> 
      list_application_to_string (mark_top <<- lf_type_head_to_string) (lf_expr_to_string_with_subs subs) (hd,args)

let rec lf_kind_to_string_with_subs subs = function
  | ( K_ulevel | K_expression | K_judgment | K_primitive_judgment | K_witnessed_judgment | K_judged_expression ) as k -> top_prec, List.assoc k lf_kind_constant_table
  | K_Pi(v,t,k) -> 
      let used = occurs_in_kind v k in
      let w,subs = var_chooser v subs occurs_in_kind k in
      let infix = " ⟶ " in
      let infix_prec = arrow_prec in
      let t = lf_type_to_string_with_subs subs t in
      let k = lf_kind_to_string_with_subs subs k in
      if used then
        binder_prec, concat ["(";vartostring w; ":"; paren_right colon_prec t; ")";infix; paren_right binder_prec k]
      else
        infix_prec, concat [paren_left infix_prec t; infix; paren_right infix_prec k]

let spine_to_string args = paren_left bottom_prec (
  args_fold
    (fun accu arg -> spine_prec, paren_left spine_prec accu ^ ";" ^ paren_right spine_prec (lf_expr_to_string_with_subs [] arg))
    (fun accu -> spine_prec, paren_left spine_prec accu ^ ";π₁")
    (fun accu -> spine_prec, paren_left spine_prec accu ^ ";π₂")
    (top_prec,"") args)

let lf_expr_to_string e = paren_right bottom_prec (lf_expr_to_string_with_subs [] e)

let lf_type_to_string t = paren_right bottom_prec (lf_type_to_string_with_subs [] t)

let lf_kind_to_string k = paren_right bottom_prec (lf_kind_to_string_with_subs [] k)

(** Printing of TS terms in TS format. *)

let lf_expr_p e = raise NotImplemented

let locate f x =                        (* find the index of the element of the list x for which f is true *)
  let rec repeat i x =
    match x with 
    | xi :: x -> if f xi then i else repeat (i+1) x
    | [] -> raise Not_found
  in repeat 0 x

let locations f x =                     (* find the indices of all elements of the list x for which f is true *)
  let rec repeat i x =
    match x with 
    | xi :: x -> if f xi then i :: repeat (i+1) x else repeat (i+1) x
    | [] -> []
  in repeat 0 x

let apply n f =                         (* generate f 0 :: f 1 :: f 2 :: ... :: f (n-1) *)
  let rec repeat i =
    if i = n then []
    else f i :: repeat (i+1)
  in repeat 0
    
let ends_in_paren s = s.[String.length s - 1] = '['

let lf_head_to_string h = lf_head_to_string_with_subs [] h

let possible_comma accu = if (ends_in_paren accu) then accu else accu ^ ","

let rec application_to_ts_string hd args = top_prec, (
  args_fold
    (fun accu arg -> 
    possible_comma accu ^ paren_right comma_prec (ts_expr_to_string arg))
    (fun accu -> possible_comma accu ^ "CAR")	(*not right*)
    (fun accu -> possible_comma accu ^ "CDR")
    (hd ^ "[")
    args) ^ "]"

and lf_atomic_p h args = application_to_ts_string (lf_head_to_string h) args

and ts_expr_to_string e : smart_string = 
  match unmark e with 
  | CONS(x,y) -> 
      let x = ts_expr_to_string x in
      let y = ts_expr_to_string y in
      top_prec, concat ["(pair ";paren_left list_prec x;" ";paren_left list_prec y;")"] (* does not correspond to our parser *)
  | LAMBDA(v,body) -> arrow_prec, vartostring v ^ " ⟾ " ^ paren_right arrow_prec (ts_expr_to_string body)
  | APPLY(V v,END) -> top_prec, vartostring v
  | APPLY(h,args) -> 
      match h with
      | T T_Pi -> (
          match args with
          | ARG(t1,ARG((_,LAMBDA(x, t2)),END)) -> 
              if false
              then arrow_prec, concat [paren_left arrow_prec (ts_expr_to_string t1);" ⟶ ";paren_right arrow_prec (ts_expr_to_string t2)]
              else top_prec, concat ["@[" ^ expr_head_to_string h ^ ";";vartostring x;"][";
				     paren_left comma_prec (ts_expr_to_string t1);",";
				     paren_right comma_prec (ts_expr_to_string t2);"]"]
          | _ -> lf_atomic_p h args)
      | T T_Sigma -> (
          match args with ARG(t1,ARG((_,LAMBDA(x, t2)),END)) -> 
            top_prec, "@[" ^ expr_head_to_string h ^ ";" ^ vartostring x ^ "]" ^
            "(" ^ paren_left comma_prec (ts_expr_to_string t1) ^ "," ^ paren_right comma_prec (ts_expr_to_string t2) ^ ")"
          | _ -> lf_atomic_p h args)
      | O O_ev -> (
          match args with 
          | ARG(f,ARG(o,ARG((_,LAMBDA(x, t)),END))) ->
              top_prec, "[ev;" ^ vartostring x ^ "][" ^ 
	      paren_left comma_prec (ts_expr_to_string f) ^ "," ^ 
	      paren_left comma_prec (ts_expr_to_string o) ^ "," ^ 
	      paren_left comma_prec (ts_expr_to_string t) ^ "]"
          | ARG(f,ARG(o,END)) ->
              top_prec, "[ev;_][" ^ 
	      paren_left comma_prec (ts_expr_to_string f) ^ "," ^ 
	      paren_left comma_prec (ts_expr_to_string o) ^ "]"
          | _ -> lf_atomic_p h args)
      | O O_lambda -> (
          match args with 
          | ARG(t,ARG((_,LAMBDA(x,o)),END)) ->
              top_prec, "[λ;" (* lambda *) ^ vartostring x ^ "][" ^ 
	      paren_left comma_prec (ts_expr_to_string t) ^ "," ^ 
	      paren_left comma_prec (ts_expr_to_string o) ^ "]"
          | _ -> lf_atomic_p h args)
      | O O_forall -> (
          match args with 
          | ARG(u,ARG(u',ARG(o,ARG((_,LAMBDA(x,o')),END)))) ->
              top_prec, "[forall;" ^ vartostring x ^ "][" ^ 
              paren_left comma_prec (ts_expr_to_string u) ^ "," ^ 
	      paren_left comma_prec (ts_expr_to_string u') ^ "," ^ 
              paren_left comma_prec (ts_expr_to_string o) ^ "," ^ 
	      paren_left comma_prec (ts_expr_to_string o') ^ "]"
          | _ -> lf_atomic_p h args)
      | _ -> lf_atomic_p h args

(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * lf_expr) list)) 
    -> concatl [
      if List.length uexp_parms > 0 
      then ["(";
            (String.concat " " (List.map (vartostring <<- snd) uexp_parms));
            ":Univ";
            (String.concat "" (List.map 
                                 (fun (pos,(u,v)) -> concat ["; "; 
							     paren_left bottom_prec (ts_expr_to_string u); "="; 
							     paren_right bottom_prec (ts_expr_to_string v)]) 
                                 ueqns));
            ")"]
      else [];
      if List.length texp_parms > 0
      then ["("; 
            String.concat " " (List.map (vartostring) texp_parms);
            ":Type)"]
      else [];
      List.flatten (List.map 
                      (fun (v,t) -> ["(";vartostring v; ":"; 
				     paren_right colon_prec (ts_expr_to_string t);")"])
                      oexp_parms)
    ]

(** Printing of ulevel contexts. *)

let ulevel_context_to_string (UContext(uexp_parms,ueqns)) = 
    concatl [
      if List.length uexp_parms > 0 
      then [
            (String.concat " " (List.map (vartostring <<- snd) uexp_parms));
            ":Univ";
            (String.concat "" (List.map 
                                 (fun (pos,(u,v)) -> concat ["; "; 
							     paren_left bottom_prec (ts_expr_to_string u); "="; 
							     paren_left bottom_prec (ts_expr_to_string v)]) 
                                 ueqns));
            ]
      else [] ]

let ts_expr_to_string e = paren_left bottom_prec (ts_expr_to_string e)

exception Limit

let rec iteri i f = function
    [] -> ()
  | a::l -> f i a; iteri (i + 1) f l

let iteri f l = iteri 0 f l

let phantom s = String.make (String.length s) ' '

(** The following routines can be used with [printf "%a"], and are convenient for debugging. *)

let _v file x = output_string file (vartostring x)

let _v_phantom file x = output_string file (phantom (vartostring x))

let _ts file x = output_string file (ts_expr_to_string x)

let _tac file tac = output_string file (tactic_to_string tac)

let _s file x = output_string file (spine_to_string x)

let _e file x = output_string file (lf_expr_to_string x)

let _l file x = List.iter (fun x -> printf " "; _e file x) x

let _h file x = output_string file (lf_head_to_string x)

let _t file x = output_string file (lf_type_to_string x)

let _k file x = output_string file (lf_kind_to_string x)

let _th file x = output_string file (lf_type_head_to_string x)

let _pos file x = output_string file (errfmt x)

let _pos_of file x = output_string file (errfmt (get_pos x))

(** Display the signature. *)

let print_signature env file =
  fprintf file "Signature:\n";
  fprintf file "  Kind constants:\n";
  List.iter (fun (kind,name) -> 
    fprintf file "     %s : kind\n" name
           ) lf_kind_constant_table;
  fprintf file "  Type constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" _th h  _k (tfhead_to_kind h)
           ) lf_type_heads;
  fprintf file "  Object constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" _h h  _t (head_to_type env (Error.no_pos 23) h)
           ) lf_expr_heads;
  flush file

(** Print the context. *)

let print_global_lf_context file env = 
  fprintf file "Global LF Context (definitions and axioms):\n";
  VarMap.iter 
    (fun v t -> (
      match unmark t with
      | F_Singleton(e,t) ->
          fprintf file "     %a := %a\n"   _v v          _e e;
          fprintf file "     %a :  %a\n%!" _v_phantom v  _t t
      | _ -> 
          fprintf file "     %a : %a\n%!" _v v  _t t))
    env.global_lf_context

let print_context n file (c:environment) = 
  let n = match n with None -> -1 | Some n -> n in
  fprintf file "LF Context:\n";
  let env = c.lf_context in
  let env = if n < 0 then List.rev env else env in (
  try iteri
      (fun i (v,t) ->
        if i = n then raise Limit;
        match unmark t with
        | F_Singleton(e,t) ->
            fprintf file "   %a := %a\n"   _v v          _e e;
            fprintf file "   %a  : %a\n%!" _v_phantom v  _t t
        | _ -> 
            fprintf file "   %a : %a\n%!" _v v  _t t
      ) 
      env
  with Limit -> fprintf file "   ...\n");
  fprintf file "TS Context:\n";
  let env = c.ts_context in
  let env = if n < 0 then List.rev env else env in (
  try iteri
      (fun i (v,t) ->
        if i = n then raise Limit;
	fprintf file "   %a : %a\n%!" _v v  _e t
      ) 
      env
  with Limit -> fprintf file "     ...\n");
  fprintf file "TTS Context:\n";
  let env = c.tts_context in
  let env = if n < 0 then List.rev env else env in (
  try iteri
      (fun i (p,o,t) ->
        if i = n then raise Limit;
	fprintf file "   %a : %a : %a\n%!" _v p _v o _e t
      ) 
      env
  with Limit -> fprintf file "     ...\n");
  if n = -1 then print_global_lf_context file c

let print_surroundings (surr:surrounding) = 
  printf "Surroundings:\n";
  let show_surr (i,e,t) =
    (match i with 
    | S_projection i -> printf "     projection pi_%d\n" i
    | S_argument i -> printf "     part %d\n" i
    | S_body -> printf "     body\n");
    (match e with 
    | Some e -> printf "        in expression %a\n" _e e
    | None -> ());
    (match t with
    | Some t -> printf "        of type %a\n" _t t
    | None -> ())
  in
  List.iter show_surr surr;
  flush stdout

let prompt env =
  printf "i%d = %!" env.state

(* 
  Local Variables:
  compile-command: "make -C .. src/printer.cmo "
  End:
 *)
