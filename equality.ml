open Alpha
open Typesystem

let rec eql alpha a b = List.length a = List.length b && List.for_all2 (eq alpha) a b
and eq alpha e e' = match (e,e') with
    | LAMBDA (x,body),LAMBDA(x',body') -> let alpha = addalpha (strip_pos x) (strip_pos x') alpha in eq alpha body body'
    | ATOMIC(pos,e), ATOMIC(pos',e') -> (
	match (e,e') with

	| Variable o, Variable o' 
	  -> testalpha' o o' alpha

	|   APPLY(O O_ev,[ATOMIC(_,APPLY(O O_lambda,_)) as f ;o ;LAMBDA( x ,t )]),
	    APPLY(O O_ev,[ATOMIC(_,APPLY(O O_lambda,_)) as f';o';LAMBDA( x',t')]) 
	  -> (eq alpha f f' && eq alpha o o') || (eq alpha (Reduction.beta1 f o) (Reduction.beta1 f' o'))

	| APPLY(O O_ev,[ATOMIC(_,APPLY(O O_lambda,_)) as f;o;LAMBDA( x,t)]), e'
	  -> eq alpha (Reduction.beta1 f o) (ATOMIC(pos',e'))

	| e, APPLY(O O_ev,[ATOMIC(_,APPLY(O O_lambda,_)) as f';o';LAMBDA( x',t')])
	  -> eq alpha (ATOMIC(pos,e)) (Reduction.beta1 f' o')

	| APPLY(h,args), APPLY(h',args')
	  -> h = h' && eql alpha args args'

	| _,_ -> false)
    | _,_ -> false

let equal a b = eq [] a b

