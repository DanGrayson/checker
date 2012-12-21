
Theorem id0 { ⊢ T Type, t:T } : T ;; _ ⟼ t ⟼ t.

Theorem id0' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ;; _ ⟼ _ ⟼ t ⟼ t.

Theorem id0'' { ⊢ u Ulevel, T:[U](u), t:*T } : *T ; _ ⟾ _ ⟾ t ⟾ t.

Theorem id1 { ⊢ T Type, t:T} ⊢ t : T ; _ ⟾ t ⟾ t.

Theorem id1' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ;; _ ⟼ _ ⟼ t ⟼ t.

Theorem id1'' { ⊢ u Ulevel, T:[U](u), t:*T } ⊢ t : *T ; _ ⟾ _ ⟾ t ⟾ t.

Theorem id2 { ⊢ T U Type, f:T⟶U } : T⟶U ;; _ ⟼ _ ⟼ f ⟼ f.

Theorem id2' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U } : *T⟶*U ;; _ ⟼_ ⟼ _ ⟼ f ⟼ f.

Theorem id3 { ⊢ T Type, U Type, f:T⟶U, t:T } : U ;; T ⟼ U ⟼ f ⟼ t ⟼ (ev T U f t).

Check LF ev_hastype.

Theorem id3' { ⊢ u Ulevel, T:[U](u) }{ ⊢ U:[U](u), f:*T⟶*U, t:*T} : *U ;;
		u ⟼ T ⟼ U ⟼ f ⟼ t ⟼ (ev (El_istype u T) (El_istype u U) f t).

Theorem compose0  { ⊢ T Type, U Type, V Type, g:U⟶V, f:T⟶U, t:T } : V ;;
		T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ (ev U V g (ev T U f t)).

Theorem compose0' { ⊢ u Ulevel, T:[U](u), U:[U](u), V:[U](u), g:*U ⟶ *V, f:*T ⟶ *U, t:*T } : *V ;; 
		u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ (ev (El_istype u U) (El_istype u V) g (ev (El_istype u T) (El_istype u U) f t)).

End.

Theorem compose0' (u Ulevel)
			(T U V:[U](u)) 
			(g : *[∀;x](u,u,U,V))
			(f : *[∀;x](u,u,T,U)) (t:*T) : *V ;;

	 (ev (El u U) (El u V) (cast2 (El u (forall u u U (pair (_ ⟼ V _1) (_ ⟼ _ ⟼ V _2) ))) _ _ g) (ev (El u T) (El u U) f t)).

End.

       compose0 = (T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ (ev U V g (ev T U f t)))

       compose0 : (T:(T0:texp) × istype T0) ⟶ 
       		  (U:(U0:texp) × istype U0) ⟶ 
		  (V:(V0:texp) × istype V0) ⟶ 
		  ((g:oexp) × hastype g ([∏] U₁ (_ ⟼ V₁))) ⟶ 
		  ((f:oexp) × hastype f ([∏] T₁ (_ ⟼ U₁))) ⟶ 
		  ((t:oexp) × hastype t T₁) ⟶ 
		  (o:oexp) × hastype o V₁

In new syntax it would be:

Theorem compose0 :: [ T Type ] =>
   		    [ U Type ] =>
   		    [ V Type ] =>
		    [ g : U ⟶ V ] =>
		    [ f : T ⟶ U ] =>
		    [ t : T ] =>
		    ?

and it could be abbreviated to 

Theorem compose0 :: [ T U V Type ] =>
   		    [ U Type ] =>
   		    [ V Type ] =>
		    [ g : U ⟶ V ] =>
		    [ f : T ⟶ U ] =>
		    [ t : T ] =>
		    ?


We have this code in two places.  We should just parse theorem parameters into the right thing, using the LF in TS syntax.

End.

# dependent version like this?:

Theorem id (T Type) (U:T ⟶ Type) (g: forall (t:T), U t) (t:T) : U t .

# or like this?:

Theorem id (T Type) (t:T ⊢ U Type) (g: forall (t:T), t\\U) (t:T) : t\\U .


Definition compose0 (T U V Type) (g:U ⟶ V) (f:T ⟶ U) (t:T) := g(f t) : V ;; (ev U V g (ev T U f t)).

End.

#Definition compose0 (T U V Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V ;; (
#       ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) $a (ev_hastype T (_ ⟼ U) f t $a $a)).

#Definition compose0' (T U V Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V ;
#       [ev_hastype](U, _ ⟾ V, g, f t, $a, [ev_hastype](T, _ ⟾ U, f, t, $a, $a)).


# Definition compose1 (T U V Type) (f:T⟶U) (g:U⟶V) := _ : T⟶V ; _.

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


Definition compose1 (T U V Type) (f:T⟶U) (g:U⟶V) := lambda x:T, (g (f x)) : T⟶V ; _.

Definition compose1 (T U V Type) (f:T⟶U) (g:U⟶V) := lambda x:T, _ : T⟶V ; _.

Definition compose1 (T U V Type) (f:T⟶U) (g:U⟶V) := lambda x:T, (g (f _)) : T⟶V ; _.


End.

Definition compose2 (T U V Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V.

Definition compose3 (T U V Type) (f:T⟶U) (g:U⟶V) := lambda x:T, (g (f _)) : T⟶V.

# in coq it looks like this:

# Definition compose1 (T U V Type) (g:U ⟶ V) (f:T ⟶ U) (t:T) : V.
# Proof.
#  apply g. apply f. assumption.
# Qed.




#   Local Variables:
#   compile-command: "make run3 "
#   End:
