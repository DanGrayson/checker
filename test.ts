# this is a comment

oPrint x.
tPrint T.
tPrint [El](x).
tPrint [U](u4).
oPrint [j](u1, u2).
tPrint *[u](u4).
uPrint max((u1+1+0)+4,2).
tPrint [Sigma;x](T,T').
tPrint Sigma x:T, Sigma y:U, V -> W .
tPrint [Coprod](T,T').
tPrint [Coprod;x,x'](T,T',U,U',o).
tPrint [Empty]().
tPrint [IC;x,y,z](A,a,B,D,q).
tPrint [Id](T,x,y).

oPrint [forall;x](u1,u2,o,o').

tPrint Pi x : T1, [U](14).
tPrint *x.
oPrint lambda x : T, e.

oPrint lambda f:T->U, lambda o:T, f o.
oPrint lambda g:T -> *k, lambda f:(Pi t:T, *g t), lambda o:T, f o.

oPrint lambda f:T->U, lambda o:T, lambda x : *r, f o.
tPrint A->B->C.

Tau [u](u4).
Tau [j](u,u').
Tau [ev;x](f,o,T).
Tau [ev;x](f,o,*x).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,o,o').

oDefinition E1 (u:Univ)(X:Type)(x:X) := x : X.
tDefinition E2 (u1 u2 u3:Univ)(X:Type) := X->X .
tDefinition E3 (u1 u2 u3 : Univ)(X1:Type)(x1: X1 -> [U](u1))(x2: [U](1)) := [U](u2) .
oDefinition E5 (u1 u2 u3 : Univ; max(u1,u2)=max(u2,u3); u1 >= u2+1 )(X1:Type)(x1: X1 -> [U](u1))(x2: [U](1)) := j (x1, x2) : [U](u2) .
oDefinition E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t.
oDefinition E7 (T U:Type)(t:T)(g:T -> [U](0))(u:U)(f:Pi x:T,*g x) :=  f t.
oDefinition E6 (u1 u2 u3 : Univ)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](1)) := j (x1, x2) .
Exit.
