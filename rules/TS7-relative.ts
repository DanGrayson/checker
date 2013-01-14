# -*- coding: utf-8 -*-

Mode Relative.

Include "rules/TS6.ts".

# resizing rules
# @[rr0], @[rr1]

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

	   := T ⟾ U ⟾ (_,T' ⟾ U' ⟾ ∏_istype[T, _ ⟾ U, CDR, T', _ ⟾ _ ⟾ U']).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

	   := T ⟾ U ⟾ o ⟾ (_, T' ⟾ U' ⟾ λ_hastype[T, _ ⟾ U, o, CDR, T', _ ⟾ _ ⟾ U']).

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @[ev;_][f,o,U] : U

	   := T ⟾ U ⟾ f ⟾ o ⟾ (_, T' ⟾ U' ⟾ ev_hastype[T, _ ⟾ U, f, o, CDR, T', _ ⟾ _ ⟾ U']).

Check LF ev_hastype.

End.							    # unfinished, compare with TS7.ts

#   Local Variables:
#   compile-command: "make -C .. rules7r "
#   End:
