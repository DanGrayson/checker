open Error
open Variables
open Typesystem

type alpha_eq = (var * var) list

let addalpha x x' (alpha:alpha_eq) = if x=x' then alpha else (x, x') :: alpha

type relation = (var * var) list

let testalpha (x:var) (x':var) (alpha:relation) =
  let rec test (alpha:relation) =
    match alpha with
    | [] -> x=x'
    | (v,v') :: alpha -> if x=v then x'=v' else if x'=v' then false else test alpha
  in test alpha

module type S =
  sig
    val uequiv     : uContext -> lf_expr -> lf_expr -> bool
    val term_equiv : uContext -> lf_expr -> lf_expr -> bool
    val type_equiv : uContext -> lf_type -> lf_type -> bool
  end

module Make(Ueq: Universe.Equivalence) : S = struct

  let uequiv = Ueq.term_equiv
    
  let rec term_eq ulevel_context alpha =
    let rec term_eq alpha x y = 
      match (unmark x, unmark y) with 
      | LAMBDA (x,body), LAMBDA (x',body') ->
	  let alpha = addalpha x x' alpha 
	  in term_eq alpha body body'
      | EVAL(h,args), EVAL(h',args') -> (
	  match (h,h') with
	  | V t, V t' -> testalpha t t' alpha && Helpers.args_equal (term_eq alpha) args args'
	  | U _, U _ -> uequiv ulevel_context x y
	  | _ -> h = h' && Helpers.args_equal (term_eq alpha) args args')
      | CONS(x,y), CONS(x',y') ->
	  term_eq alpha x x' && term_eq alpha y y'
      | _,_ -> false
    in term_eq alpha
    
  let rec type_eq ulevel_context alpha = 
    let rec type_eq alpha (_,x) (_,y) = x = y || match (x, y) with 
    | F_Singleton (x,t) , F_Singleton (x',t') ->
	term_eq ulevel_context alpha x x' && type_eq alpha t t'
    | F_Pi(x,t,u), F_Pi(x',t',u') ->
	type_eq alpha t t' &&
	let alpha = addalpha x x' alpha 
	in type_eq alpha u u'
    | F_APPLY(h,args), F_APPLY(h',args') ->
	h = h' && List.for_all2 (term_eq ulevel_context alpha) args args'
    | _ -> false
    in type_eq alpha

  let term_equiv ulevel_context = term_eq ulevel_context []

  let type_equiv ulevel_context = type_eq ulevel_context []

end


module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)
