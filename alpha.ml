open Typesystem

type alpha_eq = (var' * var') list

let addalpha x x' (alpha:alpha_eq) = if x=x' then alpha else (x, x') :: alpha

let testalpha' x x' =
  let rec test = ( 
    function
	[] -> x=x'
      | (y,y') :: alpha -> if x=y then x'=y' else if x'=y' then false else test alpha)
    in test
let testalpha  x x' = let x = strip_pos x and x' = strip_pos x' in testalpha' x x'

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
	  | Variable t,Variable t' -> testalpha' t t' alpha
	  | (a,a') -> a = a')
      | _ -> false
    in eq alpha

  let equiv ulevel_context = eq ulevel_context []

end


module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)
