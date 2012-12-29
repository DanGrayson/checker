# -*- coding: utf-8 -*-

# All the base judgments, and what would satisfy them as evidence.
# The binders are present in order to produce well-formed types.
# ( Here "with" means a satisfactory term would be a pair. )

Check TS : (T:texp) =>             [ T Type ].          # a proof that T is a type

Check TS : (T:texp) =>             |- T Type.           # T with a proof that T is a type

Check TS :                         Type.                # a t-expression with a proof that it is a type

Check TS : (T:texp) => (t:oexp) => [ t : T ].           # a proof that t has type T

Check TS : (T:texp) => (t:oexp) => |- t : T.            # t with a proof that t has type T

Check TS : (T:texp) =>             : T.                 # an o-expression with a proof that it has type T

Check TS : (T:texp) => (U:texp) => [ T = U ].           # a proof that T = U (type equality)

Check TS : (T:texp) => (t:oexp) 
                    => (u:oexp) => [ t = u : T ].       # a proof that t = u : T (object equality)

# Here are the base judgments again, but this time with binders for pairs.  For example,
# { |- T Type } denotes a parameter T whose value is a t-expression with a proof that it is a type.

Check TS : { |- T Type }        [ T Type ].             # T with a proof that T is a type

Check TS : { |- T Type }        |- T Type.              # T with a proof that T is a type

Check TS :                      Type.                   # a t-expression with a proof that it is a type

Check TS : { |- T Type, t:T }   [ t : T ].              # a proof that t has type T

Check TS : { |- T Type, t:T }   |- t : T.               # t with a proof that t has type T

Check TS : { |- T Type }        : T.                    # an o-expression with a proof that it has type T

Check TS : { |- T U Type }      [ T = U ].              # a proof that T = U (type equality)

Check TS : { |- T Type, t u:T } [ t = u : T ].          # a proof that t = u : T (object equality)

# Here are the judgments involving ulevel equality:

Check TS : (T:texp) => (t:oexp) => 
      		       (u:oexp) => [ t ~ u : T ].       # ulevel equivalence for o-expressions
Check TS : (T:texp) => (U:texp) => [ T ~ U Type ].      # ulevel equivalence for t-expressions
Check TS : (u:uexp) => (v:uexp) => [ u ~ v Ulevel ].    # ulevel equivalence for u-expressions

Check TS : { |- T Type, t u:T }    [ t ~ u : T ].       # ulevel equivalence for o-expressions
Check TS : { |- T U Type }         [ T ~ U Type ].      # ulevel equivalence for t-expressions
Check TS : { |- u v Ulevel }       [ u ~ v Ulevel ].    # ulevel equivalence for u-expressions

# Sample theorems demonstrating the syntax.

Definition Pt Type ::= Pt_istype .

#Theorem compose1  { ⊢ T Type, U Type, V Type, f:T⟶U, g:U⟶V, t:T } : V ::=
#                T ⟼ U ⟼ V ⟼ f ⟼ g ⟼ t ⟼ 
#                (ev U V g (ev T U f t)).


# So now we try using ev instead of ev to prove compose1' again.  Note that we don't have to use [ev],
# but the normalized form of the proof term has ([ev] g ([ev] f t (_ ⟼ U)) (_ ⟼ V)) as its first component.
Theorem LF compose1'' : T Type |- U Type |- V Type |- f :: ([Pi] T U) |- g :: ([Pi] U V) |- t :: T |- v :: V := 
        T ⟼ U ⟼ V ⟼ f ⟼ g ⟼ t ⟼ 
	(pair (ev U V g (ev T U f t CAR) CAR) 
              T' ⟼ U' ⟼ V' ⟼ f' ⟼ g' ⟼ t' ⟼ 
 	      (ev U V g (ev T U f t CAR) CDR U' V' g' (ev T U f t CDR T' U' f' t'))).

# compose1 is no use in proving the following theorem, because the first thing we need is the TS term of type oexp ⟶ oexp,
# so we use compose1' instead.  That illustrates what's wrong with our theorem syntax.
#Theorem compose1a { ⊢ T Type, U Type, V Type, g:U⟶V, f:T⟶U } : T->V ::=
#                  T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ 
#		  (λ_hastype 
#			     T V 
#			     (pair (t |-> (compose1' T_1 U_1 V_1 f_1 g_1 t CAR)) 
#			           (t |-> t' |-> (compose1' T_1 U_1 V_1 f_1 g_1 t CDR T_2 U_2 V_2 f_2 g_2 t')))).
#

#Theorem compose2 { ⊢ u Ulevel, T:[U](u), U:[U](u), V:[U](u), g:*U ⟶ *V, f:*T ⟶ *U, t:*T } : *V ::= 
#                u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
#                (ev (El_istype u U) (El_istype u V) g (ev (El_istype u T) (El_istype u U) f t)).
#
#Lemma A { |- u Ulevel, T U : [U](u), f : *[∀;x](u,u,T,U) } : [Pi;_](*T,*U) ::=
#                 u ⟼ T ⟼ U ⟼ f ⟼ 
#		 (cast (El_istype u (forall u u T U)) 
#                       (∏i (El_istype u T) (El_istype u U))
#                       (El_istype_forall_reduction u u T U)
#		       f).
#
#Theorem compose3 { |- u Ulevel, T U V : [U](u), g : *[∀;x](u,u,U,V), f : *[∀;x](u,u,T,U), t: *T } : *V ::=
#                 u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
#                 (ev (El_istype u U) (El_istype u V) (A u U V g) (ev (El_istype u T) (El_istype u U) (A u T U f) t)).
#
#Theorem compose4 { |- u Ulevel, T U V : [U](u), g : *[∀;x](u,u,U,V), f : *[∀;x](u,u,T,U) } : *T -> *V ::=
#                 u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ 
#		 (λ_hastype 
#			    (El_istype u T) (El_istype u V) 
#			    (compose3 u T U V g f) # <--- same problem here
#			    ).
#
#	need:
#
#	(o:oexp ⟶ oexp) × ((x:oexp) ⟶ 
#				hastype x (El_istype u (T₁,T₂))₁ ⟶ 
#				hastype (o x) (El_istype u (V₁,V₂))₁)


#Theorem A' { |- u Ulevel, T U : [U](u), f : *[∀;x](u,u,T,U) } : [Pi](*T,*U) ::=  # <-- bug here 
#                 u ⟼ T ⟼ U ⟼ f ⟼ 
#		 (cast (El_istype u (forall u u T U)) 
#                             (∏i (El_istype u T) (El_istype u U))
#                             (El_istype_forall_reduction u u T U) f).
#

#   Local Variables:
#   compile-command: "make -C .. demo "
#   End:
