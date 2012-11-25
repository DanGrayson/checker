open Typesystem

type alpha_eq = (var' * var') list

let addalpha x x' (alpha:alpha_eq) =
  let x = strip_pos_var x in
  let x' = strip_pos_var x' in 
  if x = x' then alpha
  else (x,x') :: alpha
let testalpha'  x x' alpha =
  let rec test = ( 
    function
	[] -> x=x'
      | (y,y') :: alpha -> if x=y then x'=y' else if x'=y' then false else test alpha)
  in test alpha
let testalpha  x x' = let x = strip_pos x and x' = strip_pos x' in testalpha' x x'

let rec eql alpha a b = List.length a = List.length b && List.for_all2 (eq alpha) a b
and eq alpha e e' = match (e,e') with
    | LAMBDA (x,body),LAMBDA(x',body') -> let alpha = addalpha x x' alpha in eq alpha body body'
    | POS(pos,e), POS(pos',e') -> (
	match (e,e') with

	| Variable o, Variable o' 
	  -> testalpha' o o' alpha

	|   APPLY(O O_ev,[POS(_,APPLY(O O_lambda,_)) as f ;o ;LAMBDA( x ,t )]),
	    APPLY(O O_ev,[POS(_,APPLY(O O_lambda,_)) as f';o';LAMBDA( x',t')]) 
	  -> (eq alpha f f' && eq alpha o o') || (eq alpha (Reduction.beta1 f o) (Reduction.beta1 f' o'))

	| APPLY(O O_ev,[POS(_,APPLY(O O_lambda,_)) as f;o;LAMBDA( x,t)]), e'
	  -> eq alpha (Reduction.beta1 f o) (POS(pos',e'))

	| e, APPLY(O O_ev,[POS(_,APPLY(O O_lambda,_)) as f';o';LAMBDA( x',t')])
	  -> eq alpha (POS(pos,e)) (Reduction.beta1 f' o')

	| APPLY(h,args), APPLY(h',args')
	  -> h = h' && eql alpha args args'

	| _,_ -> false)
    | _,_ -> false

let equal a b = eq [] a b

