
Theorem id0 { ⊢ T Type, t:T } : T ::= _ ⟼ t ⟼ (t, _ ⟼ t ⟼ t).

Theorem id0' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ::= _ ⟼ _ ⟼ t ⟼ (t, _ ⟼ t ⟼ t).

Theorem id0'' { ⊢ u Ulevel, T:[U](u), t:*T } : *T := _ ⟾ _ ⟾ t ⟾ (t, _ ⟾ t ⟾ t).

Theorem id1 { ⊢ T Type, t:T} ⊢ t : T := _ ⟾ t ⟾ (t, _ ⟾ t ⟾ t).

Theorem id1' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ::= _ ⟼ _ ⟼ t ⟼ (t, _ ⟼ t ⟼ t).

Theorem id1'' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T := _ ⟾ _ ⟾ t ⟾ (t, _ ⟾ t ⟾ t).

Theorem id2 { ⊢ T U Type, f:T⟶U } : T⟶U ::= _ ⟼ _ ⟼ f ⟼ (f, _ ⟼ _ ⟼ f ⟼ f).

Theorem id2' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U } : *T⟶*U ::= _ ⟼ _ ⟼ _ ⟼ f ⟼ (f, _ ⟼ _ ⟼ f ⟼ f).


# ev : (T:texp) ⟶ (U:oexp ⟶ texp) ⟶ (f:oexp) ⟶ (o:oexp) ⟶ (x:Singleton(([ev] f o (t ⟼ (U t))) : oexp)) 
# × istype T ⟶ ((t:oexp) ⟶ hastype t T ⟶ istype (U t)) ⟶ hastype f ([∏] T U) ⟶ hastype o T ⟶ hastype x (U o))


Theorem id3 { ⊢ T Type, U Type, f:T⟶U, t:T } : U ::= 
		T  ⟼ U  ⟼ f  ⟼ t  ⟼ ((ev T U f t CAR), 
		T' ⟼ U' ⟼ f' ⟼ t' ⟼  (ev T U f t CDR T' U' f' t')).

Theorem id3' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U, t:*T} : *U ::=
	u ⟼ T  ⟼ U  ⟼ f  ⟼ t  ⟼ (
		(ev (El u T CAR   ) (El u U CAR   ) f  t CAR),
            T' ⟼ U' ⟼ f' ⟼ t' ⟼  
		(ev (El u T CAR   ) (El u U CAR   ) f  t CDR 
		    (El u T CDR T') (El u U CDR U') f' t'    )).

End.

Check LF λh.

Theorem modus_ponens { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::= 
	T |-> U |-> V |-> 
	(λh (∏i T U)
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
