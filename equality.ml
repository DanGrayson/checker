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

let rec uequal a b = a == b || ueq' (get_u a,get_u b)
and ueq' = function
  | Upos (_,u), u' -> ueq' (u,u')
  | u, Upos (_,u') -> ueq' (u,u')
  | UEmptyHole, UEmptyHole -> true
  | UNumberedEmptyHole n, UNumberedEmptyHole n' -> n = n'
  | Uvariable Var x, Uvariable Var x' -> x = x'
  | Uplus (x,n), Uplus (x',n') -> ueq' (x,x') && n = n'
  | Umax (x,y), Umax (x',y') -> ueq' (x,x') && ueq' (y,y')
  | U_def (d,u), U_def (d',u') -> raise Error.NotImplemented
  | _ -> false

let rec eql alpha a b = List.length a = List.length b && List.for_all2 (eq alpha) a b
and eq alpha e e' = match (e,e') with
    | LAMBDA (x,bodies),LAMBDA(x',bodies') -> let alpha = addalpha x x' alpha in eql alpha bodies bodies'
    | POS(pos,e), POS(pos',e') -> (
	match (e,e') with

	| UU u, UU u' 
	  -> ueq' (u,u')

	| TT_variable t, TT_variable t' 
	  -> t = t'

	| OO_variable o, OO_variable o' 
	  -> testalpha' o o' alpha

	|   APPLY(OO OO_ev,[POS(_,APPLY(OO OO_lambda,_)) as f ;o ;LAMBDA( x ,[t ])]),
	    APPLY(OO OO_ev,[POS(_,APPLY(OO OO_lambda,_)) as f';o';LAMBDA( x',[t'])]) 
	  -> (eq alpha f f' && eq alpha o o') || (eq alpha (Reduction.beta1 f o) (Reduction.beta1 f' o'))

	| APPLY(OO OO_ev,[POS(_,APPLY(OO OO_lambda,_)) as f;o;LAMBDA( x,[t])]), e'
	  -> eq alpha (Reduction.beta1 f o) (POS(pos',e'))

	| e, APPLY(OO OO_ev,[POS(_,APPLY(OO OO_lambda,_)) as f';o';LAMBDA( x',[t'])])
	  -> eq alpha (POS(pos,e)) (Reduction.beta1 f' o')

	| APPLY(h,args), APPLY(h',args')
	  -> h = h' && eql alpha args args'

	| _,_ -> false)
    | _,_ -> false

let equal a b = eq [] a b

