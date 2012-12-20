# -*- coding: utf-8 -*-

# the derivation rules for TS0

Rule 7 tsimeq { ⊢ T Type } { ⊢ U Type } [ T ~ U Type ] ⇒ [ T = U ].

Rule 8 teqsymm { ⊢ T Type } { ⊢ U Type } [ U = T ] ⇒ [ T = U ].

Rule 9 teqtrans { ⊢ T Type } { ⊢ U Type } { ⊢ V Type } [ T = U ] ⇒ [ U = V ] ⇒ [ T = V ].

Rule 10 osimeq { ⊢ T Type } { ⊢ x : T } { ⊢ y : T } [ x ~ y ] ⇒ [ x = y : T ].

Rule 11 oeqsymm { ⊢ T Type } { ⊢ x : T } { ⊢ y : T } [ x = y : T ] ⇒ [ y = x : T ].

Rule 12 oeqtrans { ⊢ T Type } { ⊢ x : T } { ⊢ y : T } { ⊢ z : T } [ x = y : T ] ⇒ [ y = z : T ] ⇒ [ x = z : T ].

Rule 13 cast { ⊢ T Type } { ⊢ U Type } { ⊢ o : T } [ T = U ] ⇒ [ o : U ].

Rule 14 oeqcast { ⊢ T Type } { ⊢ U Type } { ⊢ x : T } { ⊢ y : T } [ x = y : T ] ⇒ [ T = U ] ⇒ [ x = y : U ].

Rule 15 U_istype { ⊢ M Ulevel } ⊢ [U](M) Type.

Rule 16 u_hastype { ⊢ M Ulevel } ⊢ [u](M) : [U]([next](M)).

Rule 17 El_istype { ⊢ M Ulevel } { ⊢ o : [U](M) } ⊢ [El](o) Type.

Rule 18 El_u_reduction { ⊢ M Ulevel } [ [El]([u](M)) = [U](M) ].

Rule 19 El_eq { ⊢ M Ulevel } { |- x : [U](M) } { |- y : [U](M) } [ x = y : [U](M) ] ⇒ [ [El](x) = [El](y) ].

Rule 20 El_eq_reflect { ⊢ M Ulevel } { |- x : [U](M) } { |- y : [U](M) } [ [El](x) = [El](y) ] ⇒ [ x = y : [U](M) ].

Rule 21 ∏_istype { |- T Type } { _ : T |- U Type } |- [∏](T,U) Type .

Rule 22.1 ∏_eq1 { |- T Type } { |- T' Type } { _ : T |- U Type } [ T = T' ] => [ [∏](T,U) = [∏](T',U) ].

Rule 22.2 ∏_eq2 { |- T Type } { _ : T |- U Type } { _ : T |- U' Type } ( { |- x : T } [ U/x = U'/x ] ) => [ [∏](T,U) = [∏](T,U') ].

Rule 23 λ_hastype { |- T Type } { _ : T |- U Type } { x : T |- o : U/x } |- [λ](T,o) : [∏](T,U).

Rule 24.1 λ_equality1 { |- T Type } { |- T' Type } { _ : T |- U Type } { x : T |- o : U/x }

     			[ T = T' ] => [ [λ](T,o) = [λ](T',o) : [∏](T,U) ].

Rule 24.2 λ_equality2 { |- T Type } { _ : T |- U Type } { _ : T |- U' Type } { x : T |- o : U/x }  { x : T |- o' : U/x } 

     			( { |- x : T } [ o/x = o'/x : U/x ] ) => [ [λ](T,o) = [λ](T,o') : [∏](T,U) ].

Rule 25 ev_hastype { |- T Type } { _ : T |- U Type } { |- f : [∏](T,U) } { |- o : T } |- [ev](f,o,U) : U/o.

Rule 25.1 ev { |- T Type } { |- U Type } { |- f : [∏;_](T,U) } { |- o : T } |- [ev;_](f,o,U) : U.  # non-dependent version

Rule 26 ev_eq :: ∏ T : texp, ∏ U : oexp ⇒ texp, ∏ f : oexp, ∏ o : oexp,

     ∏ T' : texp, ∏ U' : oexp ⇒ texp, ∏ f' : oexp, ∏ o' : oexp,

     (∏ x:oexp, [ x : T ] ⇒ [ (U x) = (U' x) ]) ⇒ 

     [ f = f' : ([∏] T U) ] ⇒ 

     [ o = o' : T ] ⇒ 

     [ ([ev] f o U) = ([ev] f' o' U') : (U o)].

Rule 27 beta_reduction :: ∏ T : texp, ∏ U : oexp ⇒ texp, ∏ t : oexp, ∏ f : oexp ⇒ oexp,

     [ t : T ] ⇒ 

     (∏ t':oexp, [ t' : T ] -> [ (f t') : (U t') ]) ⇒

     [ ([ev] ( [λ] T f ) t U) = (f t) : (U t) ].

Rule 28 eta_reduction :: ∏ T:texp, ∏ U:oexp ⇒ texp, ∏ f:oexp,

     [ f : ([∏] T U) ] ⇒ [ ([λ] T (x ⟼ ([ev] f x U))) = f : ([∏] T U) ].

Rule 29 j_type :: ∏ M1:uexp, ∏ M2:uexp, 

     uequal ([max] M1 M2) M2 ⇒ [ ([j] M1 M2) : ([∏] ([U] M1) (_ ⟼ ([U] M2))) ].

Rule 30 El_j_reduction :: ∏ M1:uexp, ∏ M2:uexp, ∏ o:oexp,

     [ o : ([U] M1) ] ⇒ uequal ([max] M1 M2) M2 ⇒ [ ([El]( [ev] ([j] M1 M2) o (_ ⟼ ([U] M2)) )) = ([El] o) ].

Rule 31 forall { ⊢ M1 Ulevel } { ⊢ M2 Ulevel } 

      { ⊢ o1 : [U](M1) } 

      { x : [El](o1) ⊢ o2 : [U](M2) }

      := [∀](M1,M2,o1,o2) : [U]([max](M1,M2)).

Rule 32 El_forall_reduction :: ∏ M1 : uexp, ∏ M2 : uexp, ∏ o1 : oexp, ∏ o2 : oexp ⇒ oexp,

     [ o1 : ([U] M1) ] ⇒

     (∏ x: oexp, [ x : ([El] o1) ] ⇒ [ (o2 x) : ([U] M2) ]) ⇒

     [ ([El] ([∀] M1 M2 o1 o2)) = ([∏] ([El] o1) (x ⟼ ([El] (o2 x)))) ].

Rule 32.1 El_forall :: 

     (M1 : uexp) -> (M2 : uexp) ->

     (o1 : (o1 : oexp) × hastype o1 ([U] M1)) ->

     (o2 : (o2 : oexp -> oexp) × ( (x : (x:oexp) × hastype x ([El] o1_1) ) -> hastype (o2 x_1) ([U] M2))) ->

     tequal ([El] ([∀] M1 M2 o1_1 o2_1)) ([∏] ([El] o1_1) (x ⟼ ([El] (o2_1 x)))) .

Rule 100 teq_empty_eta :: ∏ T:texp, ∏ T':texp, ∏ a:oexp,

     [ a : ([Empty]) ] ⇒ [ T Type ] ⇒ [ T' Type ] ⇒ [ T = T'].

Rule 101 oeq_empty_eta :: ∏ T:texp, ∏ x:oexp, ∏ y:oexp, ∏ a:oexp,

     [ a : ([Empty]) ] ⇒ [ x : T ] ⇒ [ y : T ] ⇒ [ x = y : T ].

Rule 200 jMM_reduction :: ∏ M1:uexp, ∏ M2:uexp,

     uequal M1 M2 ⇒ 

     [ ([j] M1 M2) = ([lambda] ([U](M1)) (x ⊢> x)) : ([∏] ([U] M1) (_ ⟼ ([U] M2))) ].

Rule 201 jj_reduction :: ∏ M1:uexp, ∏ M2:uexp, ∏ M2':uexp, ∏ M3:uexp, Pi o:oexp,

     uequal M2 M2' ⇒ 

     [ o : ([U] M1) ] ->

     [  ([ev] ([j] M2' M3) ([ev] ([j] M1 M2) o (_ ⟼ ([U] M2))) (_ ⟼ ([U] M3)))

     =  ([ev] ([j] M1 M3) o (_ ⟼ ([U] M3)))

     : ([∏] ([U] M1) (_ ⟼ ([U] M3))) ].

End.

Rule 202 forall_j_reduction :: 

     ∏ M_0:uexp, ∏ M1:uexp, ∏ M'_1:uexp, ∏ M2:uexp, 

     


#   Local Variables:
#   compile-command: "make rules "
#   End:
