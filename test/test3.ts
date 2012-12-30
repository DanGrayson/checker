
Theorem id0 { ⊢ T Type, t:T } : T ::= _ ⟼ t ⟼ (t, _ ⟼ t ⟼ t).

Theorem id0' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ::= _ ⟼ _ ⟼ t ⟼ (t, _ ⟼ t' ⟼ t').

Theorem id0'' { ⊢ u Ulevel, T:[U](u), t:*T } : *T := _ ⟾ _ ⟾ t ⟾ (t, _ ⟾ t' ⟾ t').

Theorem id1 { ⊢ T Type, t:T} ⊢ t : T := _ ⟾ t ⟾ (t, _ ⟾ t ⟾ t).

Theorem id1' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ::= _ ⟼ _ ⟼ t ⟼ (t, _ ⟼ t' ⟼ t').

Theorem id1'' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T := _ ⟾ _ ⟾ t ⟾ (t, _ ⟾ t' ⟾ t').

Theorem id2 { ⊢ T U Type, f:T⟶U } : T⟶U ::= _ ⟼ _ ⟼ f ⟼ (f, _ ⟼ _ ⟼ f' ⟼ f').

Theorem id2' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U } : *T⟶*U ::= _ ⟼ _ ⟼ _ ⟼ f ⟼ (f, _ ⟼ _ ⟼ f' ⟼ f').

Theorem id3' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U, t:*T} : *U ::=
	u ⟼ T  ⟼ U  ⟼ f  ⟼ t  ⟼ (
		(ev1 (El u T CAR   ) (El u U CAR   ) f t CAR),
            T' ⟼ U' ⟼ 
		(ev1 (El u T CAR   ) (El u U CAR   ) f t CDR 
		     (El u T CDR T') (El u U CDR U'))).

Theorem modus_ponens { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::= 
	# this is a lot longer than the proof in test4.ts
	T ⟼ U ⟼ V ⟼ 
	((lambda1 (pi1 T U CAR)
	          (pi1 (pi1 U V CAR) (pi1 T V CAR) CAR)
	          (f ⟼ (lambda1 
			   (pi1 U V CAR)
	       		   (pi1 T V CAR)
			   (g ⟼ 
				(lambda1 T V 
			   	       (t ⟼ 
					    (ev1 U V g (ev1 T U f t CAR) CAR)) CAR)) CAR)) CAR), 
	T' ⟼ U' ⟼ V' ⟼ 
        (lambda1 (pi1 T U CAR)
	         (pi1 (pi1 U V CAR) (pi1 T V CAR) CAR)
	         (f ⟼ 
		      (lambda1 
			   (pi1 U V CAR)
	       		   (pi1 T V CAR)
			   (g ⟼ 
				(lambda1 T V 
			   	       (t ⟼ 
					    (ev1 U V g (ev1 T U f t CAR) CAR)) CAR)) CAR)) CDR
		(pi1 T U CDR T' U')
		(pi1 (pi1 U V CAR) (pi1 T V CAR) CDR (pi1 U V CDR U' V') (pi1 T V CDR T' V'))
		(f ⟼ f' ⟼ 
		       (lambda1 
			   (pi1 U V CAR)
	       		   (pi1 T V CAR)
			   (g ⟼ 
				(lambda1 T V 
			   	       (t ⟼ 
					    (ev1 U V g (ev1 T U f t CAR) CAR)) CAR)) CDR
 					    (pi1 U V CDR U' V')
 					    (pi1 T V CDR T' V')
			(g ⟼ g' ⟼ 
			   (lambda1 T V 
			   	       (t ⟼ 
					    (ev1 U V g (ev1 T U f t CAR) CAR)) CDR T' V' 
					(t ⟼ t' ⟼ 
					    (ev1 U V g (ev1 T U f t CAR) CDR 
					         U' V' g' (ev1 T U f t CDR T' U' f' t'))))))))).

End.


#   Local Variables:
#   compile-command: "make -C .. run3 DEBUG=no"
#   End:
