Print_o x.
Print_t T.
Print_t [El](x).
Print_t [U](u4).
Print_o [j](u1, u2).
Print_t *[u](u4).
Print_u umax((u1+1+0)+4,2).
Print_t [Sigma;x](T,T').
Print_t [Coprod](T,T').
Print_t [Coprod;x,x'](T,T',U,U',o).
Print_t [Empty]().
Print_t [IC;x,y,z](A,a,B,D,q).
Print_t [Id](T,x,y).

Print_o [forall;x](u1,u2,o,o').

Print_t Pi x : T1, [U](14).
Print_t *x.
Print_o lambda x : T, e.
Print_o lambda f:T->U, lambda o:T, lambda x : *r, f o.
Print_t A->B->C.

Tau [u](u4).
Tau [j](u,u').
Tau [ev;x](f,o,T).
Tau [ev;x](f,o,*x).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,o,o').

Definition Exmpl (u1,u2,u3 : ulevel)(X1:Type)(x1: X1 -> [U](u1))(x2: [U](1)) := [U](u2) .
Definition Exmpl (u1,u2,u3 : ulevel)(X1:Type)(x1: X1 -> [U](u1))(x2: [U](1)) := j (x1, x2) : [U](u2) .
Definition Exmpl (u1,u2,u3 : ulevel; max(u1,u2)=max(u2,u3); u1 >= u2+1 )(X1:Type)(x1: X1 -> [U](u1))(x2: [U](1)) := j (x1, x2) : [U](u2) .
