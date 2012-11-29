open Typesystem

type alpha_eq = (var' * var') list

let addalpha x x' (alpha:alpha_eq) = if x=x' then alpha else (x, x') :: alpha

type relation = (var' * var') list

let testalpha (x:var') (x':var') (alpha:relation) =
  let rec test (alpha:relation) =
    match alpha with
    | [] -> x=x'
    | (v,v') :: alpha -> if x=v then x'=v' else if x'=v' then false else test alpha
  in test alpha

module Make(Ueq: Universe.Equivalence) = struct

  let uequiv = Ueq.equiv
    
  let rec eq ulevel_context alpha =
    let rec eq alpha x y = x = y || match (x, y) with 
      | LAMBDA (x,body), LAMBDA (x',body') ->
	  let alpha = addalpha (strip_pos x) (strip_pos x') alpha 
	  in eq alpha body body'
      | ATOMIC(_,d), ATOMIC(_,e) -> (
	  d == e || 
	  match (d,e) with
	  | APPLY(h,args), APPLY(h',args') -> (
	      match (h,h') with
	      | U _, U _ -> uequiv ulevel_context x y
	      | _ -> h = h' && List.length args = List.length args' && List.for_all2 (eq alpha) args args')
	  | Variable t,Variable t' -> testalpha t t' alpha
	  | (a,a') -> a = a')
      | _ -> false
    in eq alpha

  let equiv ulevel_context = eq ulevel_context []

end


module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)
