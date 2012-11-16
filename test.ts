# this is a comment

Variable u0 u1 u2 : Univ ; u0 <= u1; u0 <= u2 .
Variable T T' T1 T2 U U' V V' W W' A B C D X Y : Type.
Show.

oCheck lambda x:T, lambda y:U, [odef;foo](u1,u2;T,U;x,y).

oCheck lambda x:T, x.
tCheck T.
tCheck [El]([u](u2)).
tCheck [U](u4).
oCheck [j](u1, u2).
tCheck *[u](u1).
uCheck max(u1+1+0+4,u0).
tCheck [Sigma;x](T,T').
tCheck Sigma x:T, Sigma y:U, V -> W .
tCheck [Coprod](T,T').
tCheck [Coprod;x,x'](T,T',U,U',[u](u0)).
tCheck [Empty]().
oCheck lambda a:A, lambda q:B, lambda t:[IC;x,y,z](A,a,B,D,q), t.
oCheck lambda x:T, lambda y:T, lambda t:[Id](T,x,y), t.

oCheck lambda o:T, lambda o':T, [forall;x](u1,u2,o,o').

tAlpha Pi x:T, U  ==  Pi y:T, U .
oAlpha lambda g:T->U, lambda x:T, g x
   ==  lambda h:T->U, lambda y:T, h y  .
oAlpha lambda g:Pi a:T, U, lambda x:T, g x
   ==  lambda h:Pi b:T, U, lambda y:T, h y  .
oAlpha lambda g:T->U, lambda x:T, g a
   ==  lambda h:T->U, lambda y:T, h y  .
oAlpha lambda g:T->U, lambda x:T, g x
   ==  lambda h:T->U, lambda y:T, h b  .
oAlpha lambda g:T->U, lambda x:T, g h
   ==  lambda h:T->U, lambda y:T, h y  .
oAlpha lambda g:T->U, lambda x:T, g x
   ==  lambda h:T->U, lambda y:T, h h  .

tCheck Pi x : T1, [U](u0+14).
tCheck Pi x : T1, [U](u0+14).

uCheck u1.
tCheck T.
oCheck lambda x:T, x.
Show.

oCheck lambda e:U, lambda x : T, e.

oCheck lambda g:T -> *[u](u1), lambda f:Pi t:T, *g t, lambda o:T, f o.

tCheck A->B->C.

oCheck lambda f:(X->X)->U, f lambda x:X, x.

Tau 14.
Tau [u](u4).
Tau [j](u,u').
Tau [j](_,u').
Tau [j](u,_).
Tau [ev;x](f,o,T).
Tau [ev;x](f,o,*x).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,o,o').

oDefinition E1 (u:Univ)(K:Type)(x:K) := x : K.
tDefinition E2 (u1 u2 u3:Univ)(K:Type) := K->K .
tDefinition E3 (u1 u2 u3 : Univ)(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [U](u2) .
oDefinition E5 (u1 u2 u3 : Univ; max(u1,u2)=max(u2,u3); u1 >= u2+1 )(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) : [U](u2) .
oDefinition E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t.
oDefinition E7 (K L:Type)(t:K)(g:K -> [U](u0))(u:L)(f:Pi x:K,*g x) := f t.
oDefinition E6 (u1 u2 u3 : Univ)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) .

oCheck lambda f:T->U, lambda o:T, [ev;_](f,o,U).
oCheck lambda f:T->U, lambda o:T, f o.
uCheck [udef;foo](u0+1,u1).
oCheck lambda x:T, lambda y:U, lambda t:[tdef;foo](u0,u0;T,U;x,y), t.
oDefinition E7 := ft.
oCheck lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
oCheck lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
oCheck lambda f:X->T, lambda y:X, f y.
oCheck lambda f:X->T, lambda y:T, f y.
