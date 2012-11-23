open Typesystem

module type S =
    sig
      val uequal : uContext -> uExpr -> uExpr -> bool
      val tequal : uContext -> expr -> expr -> bool
      val oequal : uContext -> expr -> expr -> bool
    end

module Make(Ueq: Universe.Equivalence) = struct

  type alpha_eq = (var' * var') list
	
  let addalpha x x' (alpha:alpha_eq) = if x=x' then alpha else (x, x') :: alpha
  let testalpha'  x x' =
    let rec test = ( 
      function
	  [] -> x=x'
	| (y,y') :: alpha -> if x=y then x'=y' else if x'=y' then false else test alpha)
      in test
  let testalpha  x x' = let x = strip_pos x and x' = strip_pos x' in testalpha' x x'

  let uequiv = Ueq.equiv
    
  let rec eq uc alpha =
    let rec eq alpha x y = x = y || match (x, y) with 
      | LAMBDA (x,bodies), LAMBDA (x',bodies') ->
	  let alpha = addalpha (strip_pos_var x) (strip_pos_var x') alpha 
	  in List.for_all2 (eq alpha) bodies bodies'
      | POS(_,x), POS(_,y) -> (
	  x == y || match (x,y) with
	  | APPLY(h,args), APPLY(h',args') -> (
	      match (h,h') with
	      | _ -> h = h' && List.length args = List.length args' && List.for_all2 (eq alpha) args args')
	  | UU u, UU u' -> uequiv uc u u'
	  | OO_variable t,OO_variable t' -> testalpha' t t' alpha
	  | (a,a') -> a = a')
      | _ -> false
    in eq alpha

  let equiv uc = eq uc []

end


module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)
