(** Substitution. *) 

open Typesystem

(* this doesn't yet handle replacing variables in the head position *)

let rec subst_list (subs : (var' * atomic_term) list) es = List.map (subst' subs) es
and subst (subs : (var' * atomic_term) list) ((pos,e) as d) = match e with 
  | APPLY(label,args) -> pos, APPLY(label,subst_list subs args)
  | Variable v ->(try List.assoc v subs with Not_found -> d)
  | EmptyHole _ -> d  
and subst' (subs : (var' * atomic_term) list) = function
  | ATOMIC e -> ATOMIC(subst subs e)
  | LAMBDA((pos,v), body) -> 
      let w = newfresh v in
      let v' = (pos, Variable w) in
      let subs = (v,v') :: subs in 
      LAMBDA((pos,w), subst' subs body)

let rec subst_type_list (subs : (var' * atomic_term) list) ts = List.map (subst_type subs) ts
and subst_type (subs : (var' * atomic_term) list) (pos,t) = 
  (pos,
   match t with
   | F_Pi(v,a,b) -> 
       let w = newfresh v in
       let v' = nowhere (Variable w) in
       let subs' = (v,v') :: subs in 
       F_Pi(w, subst_type subs a, subst_type subs' b)      
   | F_APPLY(label,args) -> F_APPLY(label, subst_list subs args)
   | F_Singleton(e,t) -> F_Singleton( subst' subs e, subst_type subs t )
   | F_hole -> F_hole)

(* 
  Local Variables:
  compile-command: "ocamlbuild substitute.cmo "
  End:
 *)
