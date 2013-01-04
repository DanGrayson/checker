#############################################################################

Mode Pairs.

Include "test/rules.ts".

# derive versions of some inference rules with simple types

Definition pi1 { ⊢ T U Type } ⊢ [∏;_](T,U) Type ::= 
	   (T ⟼ U ⟼ (pi₁ T (_⟼U)), T ⟼ U ⟼ (pi₂ T (_⟼U₁,_⟼U))).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ [λ](T,o) : [∏;_](T,U) ::= 
	   (T ⟼ U ⟼ (λh₁ T (_⟼U)), T ⟼ U ⟼ (λh₂ T (_⟼U₁,_⟼U))).

Definition ev1 { ⊢ T U Type, f : [∏;_](T,U), o : T } ⊢ [ev;_](f,o,U) : U ::= 
	   (T ⟼ U ⟼ (ev₁ T (_⟼U)), T ⟼ U ⟼ (ev₂ T (_⟼U₁,_⟼U))).

Theorem modus_ponens { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::= 
	(
	T ⟼ U ⟼ V ⟼ (lambda1₁ (pi1₁ T U) (pi1₁ (pi1₁ U V) (pi1₁ T V))
			      (f ⟼ (lambda1₁ (pi1₁ U V) (pi1₁ T V) 
					(g ⟼ (lambda1₁ T V (t ⟼ (ev1₁ U V g (ev1₁ T U f t)))))))),
	T ⟼ U ⟼ V ⟼ (lambda1₂ (pi1₂ T U) (pi1₂ (pi1₂ U V) (pi1₂ T V))
			      ((f ⟼ (lambda1₁ (pi1₁ U₁ V₁) (pi1₁ T₁ V₁) 
					(g ⟼ (lambda1₁ T₁ V₁ (t ⟼ (ev1₁ U₁ V₁ g (ev1₁ T₁ U₁ f t))))))),
				(f ⟼ (lambda1₂ (pi1₂ U V) (pi1₂ T V) 
					((g ⟼ (lambda1₁ T₁ V₁ (t ⟼ (ev1₁ U₁ V₁ g (ev1₁ T₁ U₁ f₁ t))))),
					 (g ⟼ (lambda1₂ T V 	
					 	((t ⟼ (ev1₁ U₁ V₁ g₁ (ev1₁ T₁ U₁ f₁ t))),
						 (t ⟼ (ev1₂ U V g (ev1₂ T U f t)))))))))))).

Clear.

#############################################################################

Mode Relative.

Include "test/rules.ts".

# derive versions of some inference rules with simple types

Definition pi1 { ⊢ T U Type } ⊢ [∏;_](T,U) Type ::= 
	   T ⟼ U ⟼ ((pi T (_ ⟼ U) CAR), T' ⟼ U' ⟼ (pi T (_ ⟼ U) CDR T' (_ ⟼ _ ⟼ U'))).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ [λ](T,o) : [∏;_](T,U) ::=
	   T ⟼ U ⟼ o ⟼ (([λ] T o), T' ⟼ U' ⟼ (λh T (_ ⟼ U) o CDR T' (_ ⟼ _ ⟼ U'))).

Definition ev1 { ⊢ T U Type, f : [∏;_](T,U), o : T } ⊢ [ev;_](f,o,U) : U ::=
	   T ⟼ U ⟼ f ⟼ o ⟼ ((ev T (_ ⟼ U) f o CAR), T' ⟼ U' ⟼ (ev T (_ ⟼ U) f o CDR T' (_ ⟼ _ ⟼ U'))).

Theorem modus_ponens { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::= 
	# this is a lot longer than the proof in test4.ts
	T ⟼ U ⟼ V ⟼ 
	((lambda1 (pi1 T U CAR) (pi1 (pi1 U V CAR) (pi1 T V CAR) CAR)
	          (f ⟼ (lambda1 (pi1 U V CAR) (pi1 T V CAR)
			   (g ⟼ (lambda1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t CAR) CAR)) CAR)) CAR)) CAR), 
	T' ⟼ U' ⟼ V' ⟼ 
        (lambda1 (pi1 T U CAR)
	         (pi1 (pi1 U V CAR) (pi1 T V CAR) CAR)
	         (f ⟼ (lambda1 (pi1 U V CAR) (pi1 T V CAR)
			   (g ⟼ (lambda1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t CAR) CAR)) CAR)) CAR)) CDR
		(pi1 T U CDR T' U')
		(pi1 (pi1 U V CAR) (pi1 T V CAR) CDR (pi1 U V CDR U' V') (pi1 T V CDR T' V'))
		(f ⟼ f' ⟼ (lambda1 
			   (pi1 U V CAR)
	       		   (pi1 T V CAR)
			   (g ⟼ (lambda1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t CAR) CAR)) CAR)) CDR
 					    (pi1 U V CDR U' V')
 					    (pi1 T V CDR T' V')
			(g ⟼ g' ⟼ (lambda1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t CAR) CAR)) CDR T' V' 
					(t ⟼ t' ⟼ (ev1 U V g (ev1 T U f t CAR) CDR 
					               U' V' g' (ev1 T U f t CDR T' U' f' t'))))))))).


Show.

#   Local Variables:
#   compile-command: "make -C .. test3 DEBUG=no"
#   End:
