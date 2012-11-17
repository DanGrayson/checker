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
uCheck max plus1 u1 u0.
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

tCheck Pi x : T1, [U](plus1 plus1 u0).
tCheck Pi x : T1, [U](plus1 u0).

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
tDefinition E3 (u1 u2 u3 : Univ)(K:Type)(x1: K -> [U](u1))(x2: [U](plus1 u0)) := [U](u2) .
oDefinition E5 (u1 u2 u3 : Univ; max u1 u2 = max u2 u3; u1 >= plus1 u2 )(K:Type)(x1: K -> [U](u1))(x2: [U](plus1 u0)) := [j](x1, x2) : [U](u2) .
oDefinition E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t.
oDefinition E7 (K L:Type)(t:K)(g:K -> [U](u0))(u:L)(f:Pi x:K, *g x) := f t.
oDefinition E6 (u1 u2 u3 : Univ)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](plus1 u0)) := [j](x1, x2) .

oCheck lambda f:T->U, lambda o:T, [ev;_](f,o,U).
oCheck lambda f:T->U, lambda o:T, f o.
oDefinition E7 := ft.
oCheck lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
oCheck lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
oCheck lambda f:X->T, lambda y:X, [ev;_](f,y,T).
oCheck lambda f:X->T, lambda y:X, f y.
# uCheck [udef;foo](plus1 u0,u1).
# oCheck lambda x:T, lambda y:U, lambda t:[tdef;foo](u0,u0;T,U;x,y), t.
oCheck lambda t:[U](u0), lambda f: *(lambda x:[U](u0), x) t -> U, lambda o:*t, f o.
End.

       							# omitted arguments are enclosed in { }
 Parsing precedence :: |- : = * @			# use @ to indicate that omitted arguments will be included
 							# use :: to indicate judgments one level up, in the meta-type-theory
							# grouping variables in one Pi means they're independent

  Declaration of variables:

  			G :: Context
  			u :: Univ
			T :: Type
			o :: Obj

       Rule Empty :: Type.				# a constant (global variable)

        Rule uuu0 :: Univ.				# a constant

       Rule empty :: Obj.				# a constant

  Five types of judgments:

  			G |-				# this one says that G is a valid context
  			G |- T type
			G |- o : T
			G |- T = T'
			G |- o = o' : T

   Rule fetch v j :: Pi {G :: Context}, 		# if G is omitted, take it from the current context
     		     G |- v$j : T.			# here v : T is j-th rightmost entry in G for the variable v, starting with j=0.
		     					# j is a sort of de Bruijn index that needs to be updated occasionally
							# abbreviate v$0 to v

    Rule subst i :: Pi {G :: Context},			# i is the index of the variable x in the context G (?); x is not mentioned explicitly (?)
		    Pi {T :: Type},
      		    Pi {j :: G |- x : T},		# G contains x:T and j can often be obtained from G using fetch
		    Pi (U :: Type) (o :: Obj),
		    Pi (k :: G |- o : T),
		    G[o/x] |- U[o/x] type.		# this is supposed to be descriptive notation for substitution; in G[o/x] the entry x:T goes away
		    					# subst i U o k :: G[o/x] |- U[o/x] type.

          Rule ev :: Pi {G :: Context} {T U :: Type} (f o :: Obj),
  	 	     Pi m :: G |- f : Pi x:T, U,	# "Pi" knows to swallow just one comma, so there's no parsing ambiguity here
		     Pi n :: G |- o : T,
		     G |- [ev;x](f,o,U) : U[o/x].	# subst 0 U o n :: G |- U[o/x] type

       Rule tcast :: Pi {G :: Context} {T T' :: Type} (o :: Obj),               # rule 13 in the paper UPTS
		     Pi n :: G |- T = T',
		     Pi j :: G |- o : T,
		     G |- o : T'.

     Rule ocastt ::  Pi {G :: Context} {T :: Type} {o :: Obj},
		     Pi j :: G |- o : T,
		     G |- [ocast](o,j) : T.			# add this as a typing rule, too (for tau)

    Rule ocastred :: Pi {G :: Context} {T :: Type} {o :: Obj},
		     Pi j :: G |- o : T,
		     G |- [ocast](o,j) = o : T.			# add this as a reduction rule, too, or just use it manually

   Rule tetaempty :: Pi {G :: Context} (T T' :: Type),		# eta reduction for empty
		     Pi j :: G |- a : Empty,
		     G |- T = T'.

   Rule oetaempty :: Pi {G :: Context} {T :: Type} {a o o' :: Obj},		# eta reduction for empty
		     Pi j :: G |- a : Empty,
		     Pi k :: o : T,
		     Pi k' :: o' : T,
		     G |- o = o' : T.

      Rule Uintro :: Pi {G :: Context} {u :: Univ},
  		     Pi j :: G |- [U](u) : Type.

       Rule plus1 :: Pi u :: Univ, Univ.

         Rule max :: Pi u v :: Univ, Univ.

      Rule uintro :: Pi {G :: Context} {u :: Univ},
     		     G |- [u](u) : [U](u+1).

  Rule emptytype ::  Pi {G :: Context},
		     G |- empty : [U](uuu0).

   Rule starempty :: Pi {G :: Context},
		     G |- *empty = Empty.		# add this as a reduction rule, too (left to right), in some list(s) of reduction rules

Constraint bottom0 :: Pi {u :: Univ}, uuu0 <= u.	# add this "constraint" every time a new universe variable is introduced, somehow


#  Now consider how to make the following expression type check correctly, despite
#  undecidability, letting G = ( T, U, X : Type, a:Pt, f:T->U, x:X ) .
#
#  		 G |- f x : T
#
#  This is what we do, step by step:
#
#  	j1 :=	@tetaempty G X T a :: G |- X = T.
#	j2 :=	@fetch 0 :: G |- x : X.
#	j3 :=	@tcast G X T x j1 j2 :: G |- x : T.
#	j4 :=	@fetch 1 :: G |- f : T -> U.
#	j5 :=	@ocastt G T o j3 :: [ocast](x,j3) : T.
#	j6 :=	ev(x,f,[ocast](x,j3),j4,j5) :: [ev;_](f,[ocast](x,j3),U) : U.
#
#	etc., ...

oCheck forall x:*y, z.  # fix the location of the holes
