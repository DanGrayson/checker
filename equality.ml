open Typesystem

type alpha_eq = (oVar' * oVar') list

let beta1 f o = match strip_pos f with
  Expr(OO OO_lambda, [t;Expr(BB x,[b])]) -> Substitute.subst [(strip_pos_var x,o)] b
| _ -> raise InternalError

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
  | Uvariable UVar x, Uvariable UVar x' -> x = x'
  | Uplus (x,n), Uplus (x',n') -> ueq' (x,x') && n = n'
  | Umax (x,y), Umax (x',y') -> ueq' (x,x') && ueq' (y,y')
  | U_def (d,u), U_def (d',u') -> raise NotImplemented
  | _ -> false

let rec eql alpha a b = List.length a = List.length b && List.for_all2 (eq alpha) a b
and eq alpha e e' = match (e,e') with
    | POS(_,e), e' -> eq alpha e e'
    | e, POS(_,e') -> eq alpha e e'
    | UU u, UU u' -> ueq' (u,u')
    | TT_variable t, TT_variable t' -> t = t'
    | OO_variable o, OO_variable o' -> testalpha' o o' alpha
    | Expr(OO OO_ev,[f;o;Expr(BB x,[t])]),Expr(OO OO_ev,[f';o';Expr(BB x',[t'])]) ->
	(eq alpha f f' && eq alpha o o') || (eq alpha (beta1 f o) (beta1 f' o'))
    | Expr(OO OO_ev,[f;o;Expr(BB x,[t])]), e' -> eq alpha (beta1 f o) e'
    | e, Expr(OO OO_ev,[f';o';Expr(BB x',[t'])]) -> eq alpha e (beta1 f' o')
    | Expr(h,args), Expr(h',args') -> (
	match h,h' with
	| BB x,BB x' -> let alpha = addalpha x x' alpha in eql alpha args args'
	| h,h' -> h = h' && eql alpha args args')
    | _ -> false
let equal a b = eq [] a b

