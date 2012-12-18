
Theorem id0 (T:Type) (t:T) : T ;; $a.

Definition id1 (T:Type) (t:T) := t : T ;; t₂.

Theorem id2 (T U:Type) (f:T->U) : T->U ;; $a.

Theorem id3 (T U:Type) (f:T->U) (t:T) : U ;; (ev_hastype3 $3 $a $a $a).

End.

Definition id4 (T U:Type) (f:T->U) (t:T) := f t : U ;; (ev_hastype3 $3 $a $a $a).

End.

#Definition compose0 (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V ;; (
#       ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) $a (ev_hastype T (_ ⟼ U) f t $a $a)).

#Definition compose0' (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V ;
#       [ev_hastype](U, _ ⟾ V, g, f t, $a, [ev_hastype](T, _ ⟾ U, f, t, $a, $a)).


# Definition compose1 (T U V:Type) (f:T->U) (g:U->V) := _ : T->V ; _.

# =	(T ⟼ _ ⟼ U ⟼ _ ⟼ V ⟼ _ ⟼ f ⟼ _ ⟼ g ⟼ _ ⟼ (pair (?1) (?2)))
# 
# :	(T:texp) ⟶ (istype T) ⟶ (U:texp) ⟶ (istype U) ⟶ (V:texp) ⟶ (istype V) ⟶ (f:oexp) ⟶
# 
# 	(hastype f ([∏] T (_ ⟼ U))) ⟶ (g:oexp) ⟶ (hastype g ([∏] U (_ ⟼ V))) ⟶
# 
# 	(o:oexp) × hastype o ([∏] T (_ ⟼ V))

# Context:
#      h$1497 : hastype g ([∏] U (_ ⟼ V))
#      g : oexp
#      h$1496 : hastype f ([∏] T (_ ⟼ U))
#      f : oexp
#      i$1500 : istype V
#      V : texp
# ...       


Definition compose1 (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f x)) : T->V ; _.

Definition compose1 (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, _ : T->V ; _.

Definition compose1 (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f _)) : T->V ; _.


End.

Definition compose2 (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V.

Definition compose3 (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f _)) : T->V.

# in coq it looks like this:

# Definition compose1 (T U V:Type) (g:U -> V) (f:T -> U) (t:T) : V.
# Proof.
#  apply g. apply f. assumption.
# Qed.




#   Local Variables:
#   compile-command: "make run3 "
#   End:
