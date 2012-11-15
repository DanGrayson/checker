# this is a comment

Variable u0 u1 u2 : Univ ; u0 <= u1; u0 <= u2 .
Variable T T1 T2 U T' V W U' A B C D X X1 : Type.
Show.

oPrint x.
tPrint T.
tPrint [El](x).
tPrint [U](u4).
oPrint [j](u1, u2).
tPrint *[u](u4).
uPrint max(u1+1+0+4,uuu0).
tPrint [Sigma;x](T,T').
tPrint Sigma x:T, Sigma y:U, V -> W .
tPrint [Coprod](T,T').
tPrint [Coprod;x,x'](T,T',U,U',o).
tPrint [Empty]().
tPrint [IC;x,y,z](A,a,B,D,q).
tPrint [Id](T,x,y).

oPrint [forall;x](u1,u2,o,o').

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

tPrint Pi x : T1, [U](uuu0+14).
tPrint *x.
oPrint lambda x : T, e.

oPrint lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.

oPrint lambda f:T->U, lambda o:T, lambda x : *r, f o.
tPrint A->B->C.

oPrint lambda f:(X->X)->U, f lambda x:X, x.

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
tDefinition E3 (u1 u2 u3 : Univ)(K:Type)(x1: K -> [U](u1))(x2: [U](uuu0+1)) := [U](u2) .
oDefinition E5 (u1 u2 u3 : Univ; max(u1,u2)=max(u2,u3); u1 >= u2+1 )(K:Type)(x1: K -> [U](u1))(x2: [U](uuu0+1)) := [j](x1, x2) : [U](u2) .
oDefinition E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t.

# this one gives an error message with an unknown position
# oDefinition E7 := ft.

oDefinition E7 (K L:Type)(t:K)(g:K -> [U](uuu0))(u:L)(f:Pi x:K,*g x) := f t.
oDefinition E6 (u1 u2 u3 : Univ)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](uuu0+1)) := [j](x1, x2) .

oPrint lambda f:T->U, lambda o:T, [ev;_](f,o,U).
oPrint lambda f:T->U, lambda o:T, f o.
