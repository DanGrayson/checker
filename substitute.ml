(** Substitution. *) 

open Typesystem
open Error

let atomic = function
  | ATOMIC e -> e
  | LAMBDA _ -> raise NotImplemented (* Doesn't yet handle replacing variables in the head position (hereditary substitution) *)

let rec subst_list (subl : (var' * canonical_term) list) es = List.map (subst' subl) es
and subst (subl : (var' * canonical_term) list) ((pos,e) as d) = match e with 
  | APPLY(label,args) -> 
      (match label with 
       | L LF_Var v ->
	   let _ = try List.assoc v subl
	   with Not_found -> raise NotImplemented (* hereditary substitution *) 
	   in ()
       | _ -> ());
      pos, APPLY(label,subst_list subl args)
  | Variable v ->(try atomic (List.assoc v subl) with Not_found -> d)
  | EmptyHole _ -> d  
and subst' (subl : (var' * canonical_term) list) = function
  | ATOMIC e -> ATOMIC(subst subl e)
  | LAMBDA((pos,v), body) -> 
      let w = newfresh v in
      let v' = (pos, Variable w) in
      let subl = (v,ATOMIC v') :: subl in 
      LAMBDA((pos,w), subst' subl body)

let rec subst_type_list (subl : (var' * canonical_term) list) ts = List.map (subst_type subl) ts
and subst_type (subl : (var' * canonical_term) list) (pos,t) = 
  (pos,
   match t with
   | F_Pi(v,a,b) -> 
       let w = newfresh v in
       let v' = nowhere (Variable w) in
       let subs' = (v,ATOMIC v') :: subl in 
       F_Pi(w, subst_type subl a, subst_type subs' b)      
   | F_APPLY(label,args) -> F_APPLY(label, subst_list subl args)
   | F_Singleton(e,t) -> F_Singleton( subst' subl e, subst_type subl t ))

let rec subst_kind_list (subl : (var' * canonical_term) list) ts = List.map (subst_kind subl) ts
and subst_kind (subl : (var' * canonical_term) list) k = 
   match k with
   | K_type -> K_type
   | K_Pi(v,a,b) -> 
       let w = newfresh v in
       let v' = nowhere (Variable w) in
       let subs' = (v,ATOMIC v') :: subl in 
       K_Pi(w, subst_type subl a, subst_kind subs' b)      

(* 
  Local Variables:
  compile-command: "ocamlbuild substitute.cmo "
  End:
 *)
