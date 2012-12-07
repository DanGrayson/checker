(** Substitution. *) 

open Error
open Typesystem
open Names
open Printer
open Printf

let atomic = function
  | Phi e -> e
  | _ -> raise NotImplemented

let rec subst_list (subl : (var * lf_expr) list) es = List.map (subst subl) es
and subst (subl : (var * lf_expr) list) : lf_expr -> lf_expr = function
  | Phi (pos,e) as d -> (
      match e with
      | APPLY(V v,args) -> (
          try 
            let z = List.assoc v subl in
            match args with
            | [] -> z
            | args -> (
                match z with 
                | Phi(zpos,APPLY(f,brgs)) -> Phi(pos,APPLY(f, List.flatten [brgs;args]))
                | LAMBDA(v,body) as f -> apply_args pos f args
                | _ ->
                    printf "about to replace %a by %a in %a, not implemented\n"
                      p_var v
                      p_expr z
                      p_expr d; flush stdout;
                    raise (Unimplemented_expr d))
          with Not_found -> d)
      | APPLY(label,args) -> Phi(pos, APPLY(label,subst_list subl args))
      | TacticHole n -> raise Internal
      | EmptyHole _ -> d)
  | PAIR(pos,x,y) -> PAIR(pos,subst subl x,subst subl y)
  | PR1(pos,x) -> PR1(pos,subst subl x)
  | PR2(pos,x) -> PR2(pos,subst subl x)
  | LAMBDA(v, body) -> 
      if v = VarUnused
      then 
	LAMBDA(v, subst subl body)
      else
	let w = newfresh v in
	let subl = (v,var_to_lf w) :: subl in 
	LAMBDA(w, subst subl body)

and apply_args pos (f:lf_expr) (args:lf_expr list) =
  let rec repeat f args = 
    match f with
    | LAMBDA(v,body) -> (
	match args with
	| x :: args -> 
	    repeat (subst [(v,x)] body) args
	| [] -> raise (GeneralError "too few arguments"))
    | x -> (
	match args with
	| [] -> x
	| _ -> raise (GeneralError "too few arguments"))
  in repeat f args

let rec subst_type_list (subl : (var * lf_expr) list) ts = List.map (subst_type subl) ts
and subst_type (subl : (var * lf_expr) list) (pos,t) = 
  (pos,
   match t with
   | F_Pi(v,a,b) -> 
       if v = VarUnused then
	 F_Pi(v, subst_type subl a, subst_type subl b)
       else
	 let w = newfresh v in
	 let subl' = (v,var_to_lf w) :: subl in 
	 F_Pi(w, subst_type subl a, subst_type subl' b)
   | F_Sigma(v,a,b) -> 
       if v = VarUnused then
	 F_Sigma(v, subst_type subl a, subst_type subl b)
       else
	 let w = newfresh v in
	 let subl' = (v,var_to_lf w) :: subl in 
	 F_Sigma(w, subst_type subl a, subst_type subl' b)
   | F_APPLY(label,args) -> F_APPLY(label, subst_list subl args)
   | F_Singleton(e,t) -> F_Singleton( subst subl e, subst_type subl t ))

let rec subst_kind_list (subl : (var * lf_expr) list) ts = List.map (subst_kind subl) ts
and subst_kind (subl : (var * lf_expr) list) k = 
   match k with
   | K_type -> K_type
   | K_Pi(v,a,b) -> 
       if v = VarUnused
       then
	 K_Pi(v, subst_type subl a, subst_kind subl b)
       else
	 let w = newfresh v in
	 let subs' = (v,var_to_lf w) :: subl in 
	 K_Pi(w, subst_type subl a, subst_kind subs' b)

let subst sub e = subst [sub] e
let subst_type sub e = subst_type [sub] e
let subst_kind sub e = subst_kind [sub] e

(* 
  Local Variables:
  compile-command: "ocamlbuild substitute.cmo "
  End:
 *)
