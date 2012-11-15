(** In this file we implement structural comparison of expressions, modulo alpha equivalence and source code positions. *)

open Typesystem

let addalpha x x' alpha = if x=x' then alpha else (x,x') :: alpha
let testalpha x x' =
  let rec test = ( 
    function
	[] -> x=x'
      | (y,y') :: alpha -> if x=y then x'=y' else if x'=y' then false else test alpha)
  in test

let ueq a b = a = b

let rec teq alpha a b = a == b || match (a,b) with ((a,_),(b,_)) -> (a == b || teq' alpha (a,b))

and teq' alpha = function
  | (El t, El t')
    -> oeq alpha t t'
  | (Pi(t,(x,u)),Pi(t',(x',u')))
    -> teq alpha t t' && let alpha = addalpha x x' alpha in teq alpha u u'
  | (Sigma(t,(x,u)),Sigma(t',(x',u')))
    -> teq alpha t t' && let alpha = addalpha x x' alpha in teq alpha u u'
      (* end of TS0 *)
  | (T_Coprod(t,u),T_Coprod(t',u'))
    -> teq alpha t t' && teq alpha u u'
  | (T_Coprod2(t1,t2,(x1,u1),(x2,u2),o),T_Coprod2(t1',t2',(x1',u1'),(x2',u2'),o'))
    -> teq alpha t1 t1' && teq alpha t2 t2'
	&& let alpha = addalpha x1 x1' alpha in teq alpha u1 u1' 
	&& let alpha = addalpha x2 x2' alpha in teq alpha u2 u2' 
	&& oeq alpha o o'
  | (a,a')
    -> a = a'

and oeq alpha a b = a == b || match (a,b) with ((a,_),(b,_)) -> (a == b || oeq' alpha (a,b))

and oeq' alpha = function
  | Ovariable a, Ovariable b -> testalpha a b alpha
  | (O_lambda(t,(x,u)),O_lambda(t',(x',u')))
    -> teq alpha t t' && let alpha = addalpha x x' alpha in oeq alpha u u'
  | (O_ev(f,o,(x,u)),O_ev(f',o',(x',u')))
    -> oeq alpha f f' && oeq alpha o o' && let alpha = addalpha x x' alpha in teq alpha u u'
  | O_forall(m,n,o,(x,p)) , O_forall(m',n',o',(x',p'))
    -> ueq m m' && ueq n n' && oeq alpha o o'&& let alpha = addalpha x x' alpha in oeq alpha p p'
      (* end of TS0 *)
  | (a,a')
    -> a = a'

let uequal a b = ueq a b
let tequal a b = teq [] a b
let oequal a b = oeq [] a b
