open Alpha
open Variables
open Typesystem

(**
  The algorithms here are preliminary, and will have to be replaced with something better.
*)

let rec eql alpha a b = List.length a = List.length b && List.for_all2 (eq' alpha) a b

and eq alpha (pos,e) (pos',e') = (
  match (e,e') with

  | LAMBDA(x,e), LAMBDA(x',e') -> 
      let alpha = addalpha (unmark x) (unmark x') alpha in eq' alpha e e'

  | EVAL(V o,[]), EVAL(V o',END) -> testalpha o o' alpha

  |   EVAL(O O_ev,[(_,EVAL(O O_lambda,_) as f );o ;LAMBDA(x ,t )]),
      EVAL(O O_ev,[(_,EVAL(O O_lambda,_) as f');o';LAMBDA(x',t')]) 
    -> (eq alpha f f' && eq alpha o o') || (eq alpha (Reduction.beta1 f o) (Reduction.beta1 f' o'))

  | EVAL(O O_ev,[(_,EVAL(O O_lambda,_) as f); o; LAMBDA(x,t)]), e'
    -> eq alpha (Reduction.beta1 f o) (pos',e')

  | e, EVAL(O O_ev,[(_,EVAL(O O_lambda,_) as f');o';LAMBDA(x',t')])
    -> eq alpha (pos,e) (Reduction.beta1 f' o')

  | EVAL(h,args), EVAL(h',args') -> h = h' && eql alpha args args'

  | _,_ -> false)

let equal a b = eq [] a b

