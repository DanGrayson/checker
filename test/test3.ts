
Theorem id0 { ⊢ T Type, t:T } : T ::= _ ⟼ t ⟼ t.

Theorem id0' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ::= _ ⟼ _ ⟼ t ⟼ t.

Theorem id0'' { ⊢ u Ulevel, T:[U](u), t:*T } : *T := _ ⟾ _ ⟾ t ⟾ t.

Theorem id1 { ⊢ T Type, t:T} ⊢ t : T := _ ⟾ t ⟾ t.

Theorem id1' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ::= _ ⟼ _ ⟼ t ⟼ t.

Theorem id1'' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T := _ ⟾ _ ⟾ t ⟾ t.

Theorem id2 { ⊢ T U Type, f:T⟶U } : T⟶U ::= _ ⟼ _ ⟼ f ⟼ f.

Theorem id2' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U } : *T⟶*U ::= _ ⟼_ ⟼ _ ⟼ f ⟼ f.

Theorem id3 { ⊢ T Type, U Type, f:T⟶U, t:T } : U ::= T ⟼ U ⟼ f ⟼ t ⟼ (ev T U f t).

Theorem id3' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U, t:*T} : *U ::=
		u ⟼ T ⟼ U ⟼ f ⟼ t ⟼ (ev (El_istype u T) (El_istype u U) f t).

End.

Check LF λ_hastype.

Theorem modus_ponens { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::= 
	T |-> U |-> V |-> 
	(λ_hastype (∏i T U)
		   (∏i (∏i U V) (∏i T V))
		   _).  # ?
End.
		   T : texp,  Ti : istype T
		   U : texp,  Ui : istype U
		   V : texp,  Vi : istype V
		   f : oexp,  fh : hastype f ([Pi;t](T,U))
		   g : oexp,  gh : hastype f ([Pi;u](U,V))
		   let gf := [λ](T,t |-> [ev](g, [ev](f, t)))


#   Local Variables:
#   compile-command: "make -C .. run3 DEBUG=no"
#   End:
