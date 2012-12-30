
Theorem id0 { ⊢ T Type, t:T } : T ::= _ ⟼ t ⟼ (t, _ ⟼ t ⟼ t).

Theorem id0' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ::= _ ⟼ _ ⟼ t ⟼ (t, _ ⟼ t' ⟼ t').

Theorem id0'' { ⊢ u Ulevel, T:[U](u), t:*T } : *T := _ ⟾ _ ⟾ t ⟾ (t, _ ⟾ t' ⟾ t').

Theorem id1 { ⊢ T Type, t:T} ⊢ t : T := _ ⟾ t ⟾ (t, _ ⟾ t ⟾ t).

Theorem id1' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ::= _ ⟼ _ ⟼ t ⟼ (t, _ ⟼ t' ⟼ t').

Theorem id1'' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T := _ ⟾ _ ⟾ t ⟾ (t, _ ⟾ t' ⟾ t').

Theorem id2 { ⊢ T U Type, f:T⟶U } : T⟶U ::= _ ⟼ _ ⟼ f ⟼ (f, _ ⟼ _ ⟼ f' ⟼ f').

Theorem id2' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U } : *T⟶*U ::= _ ⟼ _ ⟼ _ ⟼ f ⟼ (f, _ ⟼ _ ⟼ f' ⟼ f').

# introduce non-dependent versions of Pi, lambda, and ev:

Definition arrow { ⊢ T U Type } ⊢ [∏;_](T,U) Type ::= T ⟼ U ⟼ ((∏i T (_ ⟼ U) CAR), T' ⟼ U' ⟼ (∏i T (_ ⟼ U) CDR T' (_ ⟼ _ ⟼ U'))).

Definition lambda1 { ⊢ T Type } { ⊢ U Type, o : U } ⊢ [λ;_](T,o) : [∏;t](T,U) ::=
	   T ⟼ U ⟼ o ⟼ (([λ] T (_ ⟼ o)), T' ⟼ U' ⟼ o' ⟼ (λh T (_ ⟼ U) (_ ⟼ o) CDR T' (_ ⟼ _ ⟼ U') (_ ⟼ _ ⟼ o'))).

Definition ev1 { ⊢ T U Type, f : [∏;_](T,U), o : T } ⊢ [ev;_](f,o,U) : U ::=
	   T ⟼ U ⟼ f ⟼ o ⟼ ((ev T (_ ⟼ U) f o CAR), T' ⟼ U' ⟼ f' ⟼ o' ⟼ (ev T (_ ⟼ U) f o CDR T' (_ ⟼ _ ⟼ U') f' o')).

Theorem id3' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U, t:*T} : *U ::=
	u ⟼ T  ⟼ U  ⟼ f  ⟼ t  ⟼ (
		(ev1 (El u T CAR   ) (El u U CAR   ) f t CAR),
            T' ⟼ U' ⟼ 
		(ev1 (El u T CAR   ) (El u U CAR   ) f t CDR 
		     (El u T CDR T') (El u U CDR U'))).

End.

Check LF λh.

Theorem modus_ponens { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::= 
	T ⟼ U ⟼ V ⟼ 
	(λh (∏i T U)
		   (∏i (∏i U V) (∏i T V))
		   _).  # ?
End.
		   T : texp,  Ti : istype T
		   U : texp,  Ui : istype U
		   V : texp,  Vi : istype V
		   f : oexp,  fh : hastype f ([Pi;t](T,U))
		   g : oexp,  gh : hastype f ([Pi;u](U,V))
		   let gf := [λ](T,t ⟼ [ev](g, [ev](f, t)))


#   Local Variables:
#   compile-command: "make -C .. run3 DEBUG=no"
#   End:
