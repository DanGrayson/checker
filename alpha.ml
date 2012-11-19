open Typesystem

module type S =
    sig
      val uequal : uContext -> uExpr -> uExpr -> bool
      val tequal : uContext -> tExpr -> tExpr -> bool
      val oequal : uContext -> oExpr -> oExpr -> bool
    end

module Make(Ueq: Universe.Equivalence) = struct

  type alpha_eq = (oVar' * oVar') list
	
  let addalpha x x' (alpha:alpha_eq) = if x=x' then alpha else (strip_pos x, strip_pos x') :: alpha
  let testalpha'  x x' =
    let rec test = ( 
      function
	  [] -> x=x'
	| (y,y') :: alpha -> if x=y then x'=y' else if x'=y' then false else test alpha)
      in test
  let testalpha  x x' = let x = strip_pos x and x' = strip_pos x' in testalpha' x x'

  let uequiv = Ueq.equiv
    
  let rec teq uc alpha =
    let rec teq alpha a b = a == b || let a = strip_pos a and b = strip_pos b in a == b || teq' alpha (a,b)
    and teq' alpha = function
      | T_El t, T_El t'
	-> oeq uc alpha t t'
      | T_U u, T_U u'
	-> uequiv uc u u'
      | T_Pi(t,(x,u)),T_Pi(t',(x',u'))
	-> teq alpha t t' && let alpha = addalpha x x' alpha in teq alpha u u'
      | T_Sigma(t,(x,u)),T_Sigma(t',(x',u'))
	-> teq alpha t t' && let alpha = addalpha x x' alpha in teq alpha u u'
	  (* end of TS0 *)
      | T_Coprod(t,u),T_Coprod(t',u')
	-> teq alpha t t' && teq alpha u u'
      | T_Coprod2(t1,t2,(x1,u1),(x2,u2),o),T_Coprod2(t1',t2',(x1',u1'),(x2',u2'),o')
	-> teq alpha t1 t1' && teq alpha t2 t2'
	    && let alpha = addalpha x1 x1' alpha in teq alpha u1 u1' 
	    && let alpha = addalpha x2 x2' alpha in teq alpha u2 u2' 
	    && oeq uc alpha o o'
      | a, a' -> a = a'
    in teq alpha

  and oeq uc alpha =
    let rec oeq alpha a b = a == b || let a = strip_pos a and b = strip_pos b in a == b || oeq' alpha (a,b)
    and oeq' alpha = function
      | O_variable a, O_variable b -> testalpha' a b alpha
      | (O_lambda(t,(x,u)),O_lambda(t',(x',u')))
	-> teq uc alpha t t' && let alpha = addalpha x x' alpha in oeq alpha u u'
      | (O_ev(f,o,(x,u)),O_ev(f',o',(x',u')))
	-> oeq alpha f f' && oeq alpha o o' && let alpha = addalpha x x' alpha in teq uc alpha u u'
      | O_forall(m,n,o,(x,p)) , O_forall(m',n',o',(x',p'))
	-> uequiv uc m m' && uequiv uc n n' && oeq alpha o o'&& let alpha = addalpha x x' alpha in oeq alpha p p'
	  (* end of TS0 *)
      | (a,a') -> a = a'
    in oeq alpha

  let tequiv uc = teq uc []
  let oequiv uc = oeq uc []

end


module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)
