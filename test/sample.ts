# -*- coding: utf-8 -*-

Mode Relative.

Include "rules/TS2.ts".

# Sample theorems demonstrating the syntax.

Definition Pt2 Type ::= Pt_istype.

Theorem compose1 { ⊢ T Type, U Type, V Type, f:T⟶U, g:U⟶V, t:T } : V ::=
        T ⟼ U ⟼ V ⟼ f ⟼ g ⟼ t ⟼ (
	   (ev_hastype U (_ ⟼ V) g (ev_hastype T (_ ⟼ U) f t CAR) CAR), 
                T' ⟼ U' ⟼ V' ⟼ f' ⟼ g' ⟼ t' ⟼ 
		(ev_hastype 
			U 
			(_ ⟼ V) 
			g 
			(ev_hastype T (_ ⟼ U) f t CAR) 
			CDR U' 
			(_ ⟼ _ ⟼ V') 
			g' 
			(ev_hastype T (_ ⟼ U) f t CDR T' (_ ⟼ _ ⟼ U') f' t'))).

Theorem compose1a { ⊢ T Type, U Type, V Type, g:U⟶V, f:T⟶U } : T⟶V ::=
        T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ ((λ_hastype T (_ ⟼ V) (t ⟼ (compose1 T U V f g t CAR)) CAR),
	T' ⟼ U' ⟼ V' ⟼ g' ⟼ f' ⟼ 
		(λ_hastype T (_ ⟼ V) (t ⟼ (compose1 T U V f g t CAR)) CDR T' (_ ⟼ _ ⟼ V')
	            (t ⟼ t' ⟼ (compose1 T U V f g t CDR T' U' V' f' g' t')))).

Theorem compose2 { ⊢ u Ulevel, T:UU[u], U:UU[u], V:UU[u], g:*U ⟶ *V, f:*T ⟶ *U, t:*T } : *V ::= 
         u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼  t  ⟼ 
	  ((ev_hastype 
	  	(El_istype u U CAR   )
	 	(_ ⟼ (El_istype u V CAR   )) 
		g
		(ev_hastype (El_istype u T CAR) (_ ⟼ (El_istype u U CAR)) f t CAR)
		CAR),
         T' ⟼ U' ⟼ V' ⟼ g' ⟼ f' ⟼ t' ⟼
	   (ev_hastype 
	      	(El_istype u U CAR) 
		(_ ⟼ (El_istype u V CAR   )) 
		g  
		(ev_hastype (El_istype u T CAR) (_ ⟼ (El_istype u U CAR)) f t CAR) 
		CDR
 		(El_istype u U CDR U') 
		(_ ⟼ _ ⟼ (El_istype u V CDR V')) 
		g' 
		(ev_hastype 
			(El_istype u T CAR) 
			(_ ⟼ (El_istype u U CAR)) 
			f t CDR
 			(El_istype u T CDR T') 
			(_ ⟼ _ ⟼ (El_istype u U CDR U')) 
			f' t'))).


#   Local Variables:
#   compile-command: "make -C .. sample "
#   End:
