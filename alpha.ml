(** In this file we implement structural comparison of expressions, modulo alpha equivalence and source code positions. *)

open Typesystem


let ueq : (uExpr * uExpr) -> bool = function
    _ -> false

let rec teq : (tExpr * tExpr) -> bool = function
    ((a,_),(b,_)) -> teq'(a,b)
and teq' = function
    (El t, El t') -> oeq(t,t')
  | (Sigma(t,(x,u)),Sigma(t',(x',u'))) -> teq(t,t') && teq(u,u') (* alpha not implemented yet *)
  | (Pi(t,(x,u)),Pi(t',(x',u'))) -> teq(t,t') && teq(u,u') (* alpha not implemented yet *)
  | (T_Coprod(t,u),T_Coprod(t',u')) -> teq(t,t') && teq(u,u')
  | (T_Coprod2(t1,t2,(x1,u1),(x2,u2),o),T_Coprod2(t1',t2',(x1',u1'),(x2',u2'),o'))
     -> teq(t1,t1') && teq(t2,t2') && teq(u1,u1') && teq(u2,u2') && oeq(o,o') (* alpha not implemented yet *)
  | (a,a') -> a = a'

and oeq : (oExpr * oExpr) -> bool = function
  | ((a,_),(b,_)) -> oeq'(a,b)
and oeq' = function
  | (O_lambda(t,(x,u)),O_lambda(t',(x',u'))) -> teq(t,t') && oeq(u,u') (* alpha not implemented yet *)
  | (O_ev(f,o,(x,u)),O_ev(f',o',(x',u'))) -> oeq(f,f') && oeq(o,o') && teq(u,u') (* alpha not implemented yet *)
  | (a,a') -> a = a'

let uequal a b = ueq (a,b)
let tequal a b = teq (a,b)
let oequal a b = oeq (a,b)
