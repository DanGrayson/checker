# experiment with notation for rule and inferences.

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
# tCheck [Coprod;x,x'](T,T',U,U',[u](u0)).
tCheck [Empty]().
# oCheck lambda a:A, lambda q:B, lambda t:[IC;x,y,z](A,a,B,D,q), t.
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
Tau [ev;x](f,o, x).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,o,o').

oDefinition E1 (u:Univ)(K:Type)(x:K) := x : K.
tDefinition E2 (u1 u2 u3:Univ)(K:Type) := K->K .
tDefinition E3 (u1 u2 u3 : Univ)(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [U](u2) .
oDefinition E5 (u1 u2 u3 : Univ; max(u1,u2)=max(u2,u3); u1 >= u2+1 )(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) : [U](u2) .
oDefinition E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t.
oDefinition E7 (K L:Type)(t:K)(g:K -> [U](u0))(u:L)(f:Pi x:K, *g x) := f t.
oDefinition E6 (u1 u2 u3 : Univ)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) .

oCheck lambda f:T->U, lambda o:T, [ev;_](f,o,U).
oCheck lambda f:T->U, lambda o:T, f o.
oDefinition E7 := ft.
oCheck lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
oCheck lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
oCheck lambda f:X->T, lambda y:X, [ev;_](f,y,T).
oCheck lambda f:X->T, lambda y:X, f y.
# uCheck [udef;foo](u0+1,u1).
# oCheck lambda x:T, lambda y:U, lambda t:[tdef;foo](u0,u0;T,U;x,y), t.
oCheck lambda t:[U](u0), lambda f: *(lambda x:[U](u0), x) t -> U, lambda o:*t, f o.


    Rule fetch i ::: Pi {G :: Context}, G |- o : T. 		# here o : T is the i-th judgment from the right inside G, starting with i=0.
    								# we add a deBruijn index if the same variable name occurs further to the right (?)

         Rule ev ::: Pi {G :: Context},
	      	     Pi {T :: Type},
		     Pi {x : T}, 
	      	     Pi {U :: Type},
	      	     Pi (f, o :: Object),
  	 	     Pi m :: G |- f : Pi x:T, U,
		     Pi n :: G |- o : T,
		     G |- [ev;x](f,o,U) : U.

      Rule tcast ::: Pi {G :: Context},				# rule 13 in the paper UPTS
		     Pi {T, T' :: Type},
		     Pi o :: Object,
		     Pi n :: G |- T = T',
		     Pi {j} :: G |- o : T,
		     G |- o : T'.

    Rule ocastt :::  Pi {G :: Context},
		     Pi {T :: Type},
		     Pi {o :: Object},
		     Pi j :: G |- o : T,
		     G |- [ocast](o,j) : T.			# add this as a typing rule, too (for tau)

   Rule ocastred ::: Pi {G :: Context},
		     Pi {T :: Type},
		     Pi {o :: Object},
		     Pi j :: G |- o : T,
		     G |- [ocast](o,j) = o : T.			# add this as a reduction rule, too, or just use it manually

  Rule tetaempty ::: Pi {G :: Context}, 			# eta reduction for empty
		     Pi T :: Type,
		     Pi T' :: Type,
		     Pi a : Empty,				# this mixing of levels is where undecidability comes in
		     G |- T = T'.

  Rule oetaempty ::: Pi {G :: Context}, 			# eta reduction for empty
		     Pi T :: Type,
		     Pi a : Empty,
		     Pi o o' : T,
		     G |- o = o' : T.

 Rule Emptytype :::  Pi {G :: Context},
		     G |- Empty :: Type.

 Rule emptytype :::  Pi {G :: Context},
		     G |- empty : [U](uuu0).

  Rule starempty ::: Pi {G :: Context},
		     G |- *empty = Empty.			# add this as a reduction rule, too

        Rule uuu0 :: Univ.

    Rule bottom0 ::: Pi {u :: Univ}, uuu0 <= u.			# add this as a "constraint", too


#  Now consider how to make the following expression type check correctly, despite
#  undecidability, letting G = ( T, U, X : Type, a:Pt, f:T->U, x:X ) .
#
#  		 G |- f x : T
#
#  This is what we do, step by step:
#
#  	j1 :=	@tetaempty G X T a ::: G |- X = T.
#	j2 :=	@fetch 0 ::: G |- x : X.
#	j3 :=	@tcast G X T x j1 j2 ::: G |- x : T.
#	j4 :=	@fetch 1 ::: G |- f : T -> U.
#	j5 :=	@ocastt G T o j3 ::: [ocast](x,j3) : T.
#	j6 :=	@ev(G,T,x,T,f,[ocast](x,j3),j4,j5) ::: [ev;_](f,[ocast](x,j3),U) : U.
#
#	etc., ...

oCheck forall x:*y, z.  # fix the location of the holes
