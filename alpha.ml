open Typesystem

module type S =
    sig
      val uequal : uContext -> uExpr -> uExpr -> bool
      val tequal : uContext -> tExpr -> tExpr -> bool
      val oequal : uContext -> oExpr -> oExpr -> bool
    end

module Make(Ueq: Universe.Equivalence) = struct

  type alpha_eq = (oVar' * oVar') list
	
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
    let rec eq alpha a b = a == b || eq' alpha a b
    and eq' alpha x y = match (strip_pos x, strip_pos y) with 
      | Expr(h,a), Expr(h',a') -> (
	  match (h,h') with
	  | BB x, BB x' -> (
	      let alpha = addalpha (strip_pos_var x) (strip_pos_var x') alpha 
	      in List.for_all2 (eq alpha) a a'
	     )
	  | _ -> h = h' && List.length a = List.length a' && List.for_all2 (eq' alpha) a a')
      | UU u, UU u' -> uequiv uc u u'
      | OO_variable t,OO_variable t' -> testalpha' t t' alpha
      | (a,a') -> a = a'
    in eq alpha

  let equiv uc = eq uc []

end


module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)
