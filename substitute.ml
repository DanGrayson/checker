(** Substitution. *) 

open Error
open Typesystem
open Names

let atomic = function
  | Phi e -> e
  | LAMBDA _ -> raise NotImplemented (* Doesn't yet handle replacing variables in the head position (hereditary substitution) *)

let rec subst_list (subl : (var * lf_expr) list) es = List.map (subst' subl) es
and subst (subl : (var * lf_expr) list) ((pos,e) as d) = 
  match e with 
  | APPLY(V v,[]) ->(try atomic (List.assoc v subl) with Not_found -> d)
  | APPLY(label,args) -> 
      (match label with 
       | V v -> (
	   try 
	     let _ = List.assoc v subl
	     in raise (Unimplemented_expr (Phi d)) (* hereditary substitution *) 
	   with Not_found -> ())
       | _ -> ());
      pos, APPLY(label,subst_list subl args)
  | TacticHole n -> d
  | EmptyHole _ -> d  
and subst' (subl : (var * lf_expr) list) = function
  | Phi e -> Phi(subst subl e)
  | LAMBDA(v, body) -> 
      if v = VarUnused
      then 
	LAMBDA(v, subst' subl body)
      else
	let w = newfresh v in
	let subl = (v,var_to_lf w) :: subl in 
	LAMBDA(w, subst' subl body)

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
   | F_APPLY(label,args) -> F_APPLY(label, subst_list subl args)
   | F_Singleton(e,t) -> F_Singleton( subst' subl e, subst_type subl t ))

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
let subst' sub e = subst' [sub] e
let subst_type sub e = subst_type [sub] e
let subst_kind sub e = subst_kind [sub] e

(* 
  Local Variables:
  compile-command: "ocamlbuild substitute.cmo "
  End:
 *)
