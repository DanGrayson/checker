(** In this file, we implement definitional equality. *)

open Typesystem

type alpha_eq = (oVar' * oVar') list

let beta1 f o = match strip_pos f with
  O_lambda (t,(x,b)) -> Substitute.osubst [(strip_pos x,o)] b
| _ -> raise InternalError

let addalpha x x' (alpha:alpha_eq) = if x=x' then alpha else (strip_pos x, strip_pos x') :: alpha
let testalpha'  x x' =
  let rec test = ( 
    function
	[] -> x=x'
      | (y,y') :: alpha -> if x=y then x'=y' else if x'=y' then false else test alpha)
  in test
let testalpha  x x' = let x = strip_pos x and x' = strip_pos x' in testalpha' x x'

let rec ueq a b = a == b || let a = strip_pos a and b = strip_pos b in a == b || ueq' (a,b)
and ueq' = function
  | UEmptyHole, UEmptyHole -> true
  | UNumberedEmptyHole n, UNumberedEmptyHole n' -> n = n'
  | Uvariable UVar x, Uvariable UVar x' -> x = x'
  | Uplus (x,n), Uplus (x',n') -> ueq x x' && n = n'
  | Umax (x,y), Umax (x',y') -> ueq x x' && ueq y y'
  | U_def (d,u), U_def (d',u') -> raise NotImplemented
  | _ -> false

let rec teq alpha oa ob = oa == ob || let a = strip_pos oa and b = strip_pos ob in a == b || match (a,b) with
  | Tvariable TVar t, Tvariable TVar t' -> t = t'
  | T_El t, T_El t'
    -> oeq alpha t t'
  | T_U u, T_U u'
    -> ueq u u'
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
	&& oeq alpha o o'
  | T_Empty, T_Empty -> true
  | T_IC (tA,a,(x,tB,(y,tD,(z,q)))), T_IC (tA',a',(x',tB',(y',tD',(z',q')))) -> raise NotImplemented
  | Id (t,x,y), Id (t',x',y') -> raise NotImplemented
  | T_def (d,u,t,c), T_def (d',u',t',c') -> raise NotImplemented
  | T_nat, T_nat -> true
  | _ -> false

and oeq alpha oa ob = oa == ob || let a = strip_pos oa and b = strip_pos ob in a == b || match (a,b) with
  | Ovariable a, Ovariable b -> testalpha' a b alpha
  | (O_lambda(t,(x,u)),O_lambda(t',(x',u')))
    -> teq alpha t t' && let alpha = addalpha x x' alpha in oeq alpha u u'
  | (O_ev(f,o,(x,u)),O_ev(f',o',(x',u'))) -> (
      if oeq alpha f f' && oeq alpha o o' && let alpha = addalpha x x' alpha in teq alpha u u'
      then true
      else oeq alpha (beta1 f o) (beta1 f' o')
     )
  | (O_ev(f,o,_), y) -> oeq alpha (beta1 f o) (with_pos_of ob y)
  | (y, O_ev(f,o,_)) -> oeq alpha (with_pos_of oa y) (beta1 f o)
  | O_forall(m,n,o,(x,p)) , O_forall(m',n',o',(x',p'))
    -> ueq m m' && ueq n n' && oeq alpha o o'&& let alpha = addalpha x x' alpha in oeq alpha p p'
      (* end of TS0 *)
  | O_pair (a,b,(x,t)), O_pair (a',b',(x',t')) -> raise NotImplemented
  | O_pr1 (t,(x,u),o), O_pr1 (t',(x',u'),o') -> raise NotImplemented
  | O_pr2 (t,(x,u),o), O_pr2 (t',(x',u'),o') -> raise NotImplemented
  | O_total (m1,m2,o1,(x,o2)), O_total (m1',m2',o1',(x',o2')) -> raise NotImplemented
  | O_pt, O_pt -> true
  | O_pt_r (o,(x,t)), O_pt_r (o',(x',t')) -> oeq alpha o o' && let alpha = addalpha x x' alpha in teq alpha t t'
  | O_tt, O_tt -> true
  | O_coprod (m1,m2,o1,o2), O_coprod (m1',m2',o1',o2') -> raise NotImplemented
  | O_ii1 (t,u,o), O_ii1 (t',u',o') -> raise NotImplemented
  | O_ii2 (t,u,o), O_ii2 (t',u',o') -> raise NotImplemented
  | Sum (p,q,t,u,o,(x,s)), Sum (p',q',t',u',o',(x',s')) -> raise NotImplemented
  | O_empty, O_empty -> true
  | O_empty_r (t,o), O_empty_r (t',o') -> teq alpha t t' && true (* eta rule for Empty implies o=o' *)
  | O_c (tA,a,(x,tB,(y,tD,(z,q))),b,f), O_c (tA',a',(x',tB',(y',tD',(z',q'))),b',f') -> raise NotImplemented
  | O_ic_r (tA,a,(x,tB,(y,tD,(z,q))),i,(xx,v,tS),t), O_ic_r (tA',a',(x',tB',(y',tD',(z',q'))),i',(xx',v',tS'),t') -> raise NotImplemented
  | O_ic (m1,m2,m3,oA,a,(x,oB,(y,oD,(z,q)))), O_ic (m1',m2',m3',oA',a',(x',oB',(y',oD',(z',q')))) -> raise NotImplemented
  | O_paths (m,t,x,y), O_paths (m',t',x',y') -> raise NotImplemented
  | O_refl (t,o), O_refl (t',o') -> raise NotImplemented
  | O_J (tT,a,b,q,i,(x,e,tS)), O_J (tT',a',b',q',i',(x',e',tS')) -> raise NotImplemented
  | O_rr0 (m2,m1,s,t,e), O_rr0 (m2',m1',s',t',e') -> raise NotImplemented
  | O_rr1 (m,a,p), O_rr1 (m',a',p') -> raise NotImplemented
  | O_def (d,u,t,c), O_def (d',u',t',c') -> raise NotImplemented
  | _ -> false

let uequal = ueq
let tequal a b = teq [] a b
let oequal a b = oeq [] a b
