
Theorem id0 { ⊢ T Type, t:T } : T ;; _ ⟼ t ⟼ t.

Theorem id0' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ;; _ ⟼ _ ⟼ t ⟼ t.

Theorem id0'' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ; _ ⟾ _ ⟾ t ⟾ t.

Theorem id1 { ⊢ T Type, t:T} ⊢ t : T ; _ ⟾ t ⟾ t.

Theorem id1' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ;; _ ⟼ _ ⟼ t ⟼ t.

Theorem id1'' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ; _ ⟾ _ ⟾ t ⟾ t.

Theorem id2 { ⊢ T U Type, f:T⟶U } : T⟶U ;; _ ⟼ _ ⟼ f ⟼ f.

Theorem id2' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U } : *T⟶*U ;; _ ⟼_ ⟼ _ ⟼ f ⟼ f.

Theorem id3 { ⊢ T Type, U Type, f:T⟶U, t:T } : U ;; T ⟼ U ⟼ f ⟼ t ⟼ (ev_hastype T U f t).

Theorem id3' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U, t:*T} : *U ;;
		u ⟼ T ⟼ U ⟼ f ⟼ t ⟼ (ev_hastype (El_istype u T) (El_istype u U) f t).

End.

#   Local Variables:
#   compile-command: "make run3  DEBUG=no"
#   End:
