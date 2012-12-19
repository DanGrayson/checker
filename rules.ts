# -*- coding: utf-8 -*-

# the derivation rules for TS0

Rule 7 tsimeq :: ∏ T:texp, ∏ U:texp,

     [ T Type ] ⟶ [ U Type ] ⟶ [ T ~ U Type ] ⟶ [ T = U ].

Rule 8 teqsymm :: ∏ T:texp, ∏ U:texp,

     [ T = U ] ⟶ [ U = T ].

Rule 9 teqtrans :: ∏ T:texp, ∏ U:texp, ∏ V:texp,

     [ T = U ] ⟶ [ U = V ] ⟶ [ T = V ].

Rule 10 osimeq :: ∏ x:oexp, ∏ y:oexp, ∏ T:texp,

     [ x : T ] ⟶ [ y : T ] ⟶ [ x ~ y ] ⟶ [ x = y : T ].

Rule 11 oeqsymm :: ∏ x:oexp, ∏ y:oexp, ∏ T:texp,

     [ x = y : T ] ⟶ [ y = x : T ].

Rule 12 oeqtrans :: ∏ x:oexp, ∏ y:oexp, ∏ z:oexp, ∏ T:texp,

     [ x = y : T ] ⟶ [ y = z : T ] ⟶ [ x = z : T ].

Rule 13 cast :: ∏ o:oexp, ∏ T:texp, ∏ U:texp,

     [ o : T ] ⟶ [ T = U ] ⟶ [ o : U  ].

Rule 13.2 cast2 :: 

     (T : (T:texp) * [ T Type ]) ->

     (U : (U:texp) * [ U Type ]) ->

     [ T_1 = U_1 ] -> 

     (o : (o:oexp) * [ o : T_1 ]) ->

     (e : Singleton( o_1 : oexp )) * [ e : U_1  ].

Rule 14 oeqcast :: ∏ x:oexp, ∏ y:oexp, ∏ T:texp, ∏ U:texp,

     [ x = y : T ] ⟶ [ T = U ] ⟶ [ x = y : U ].

Rule 15 U_type :: ∏ M:uexp, 

     [ ([U] M) Type ].

Rule 16 u_univ :: ∏ M:uexp,

     [ ([u] M) : ([U] ([next] M)) ].

Rule 17 El_type :: ∏ M:uexp, ∏ o:oexp,

     [ o : ([U] M) ] ⟶ [ ([El] o) Type ].

Rule 17.1 El :: 

     (M:uexp) -> (o:(o:oexp) * hastype o ([U] M)) -> (T: Singleton( ([El] o₁) : texp )) * istype T.

Rule 18 El_u_reduction :: ∏ M:uexp,

     [ ([El]([u] M)) = ([U] M) ].

Rule 19 El_eq :: ∏ M:uexp, ∏ x:oexp, ∏ y:oexp, 

     [ x = y : ([U] M) ] ⟶ [ ([El] x) = ([El] y) ].

Rule 20 El_eq_reflect :: ∏ M:uexp, ∏ x:oexp, ∏ y:oexp, 

     [ x : ([U] M) ] ⟶ [ y : ([U] M) ] ⟶ 

     [ ([El] x) = ([El] y) ] ⟶ [ x = y : ([U] M) ].

Rule 21 ∏_istype :: ∏ T:texp, ∏ U : oexp ⟶ texp,

     (∏ x:oexp, [ x : T ] ⟶ [ (U x) Type ]) ⟶ [ ([∏] T U) Type ].

Rule 22 ∏_eq :: ∏ T:texp, ∏ T':texp, ∏ U : oexp ⟶ texp, ∏ U' : oexp ⟶ texp, 

     [ T = T' ] ⟶

     (∏ x:oexp, [ x : T ] ⟶ [ (U x) = (U' x)])

     ⟶ [ ([∏] T U) = ([∏] T' U')  ].

Rule 23 λ_hastype :: ∏ T:texp, ∏ U:oexp ⟶ texp, ∏ o:oexp ⟶ oexp,

     [ T Type ] ⟶

     (∏ x:oexp, [ x : T ] ⟶ [ (o x) : (U x) ]) ⟶

     [ ([λ] T o) : ([∏] T U) ].

Rule 24 λ_equality :: ∏ T:texp, ∏ T':texp, ∏ U:oexp ⟶ texp, ∏ o:oexp ⟶ oexp, ∏ o':oexp ⟶ oexp,

     [ T = T' ] ⟶

     (∏ x:oexp, [ x : T ] ⟶ [ (o x) = (o' x) : (U x) ]) ⟶

     [ ([λ] T o) = ([λ] T o') : ([∏] T U) ].

Rule 25 ev_hastype :: ∏ T : texp, ∏ U : oexp ⟶ texp, ∏ f : oexp, ∏ o : oexp,

     [ f : ([∏] T U) ] ⟶ 

     [ o : T ] ⟶ 

     [ ([ev] f o U) : (U o)].

Rule 25.2 ev_hastype2 :: 

     (T : (T':texp) * istype T') ->

     (U : (U':oexp ⟶ texp) * (t : (t':oexp) * hastype t' T₁) -> istype (U' t₁)) ->

     (f : (f':oexp) * hastype f' ([∏] T₁ U₁)) ->

     (o : (o':oexp) * hastype o' T₁) ->

     (e: Singleton(([ev] f₁ o₁ U₁) : oexp)) * hastype e (U₁ o₁).

Rule 25.3 ev ::   # non-dependent version

     (T : (T':texp) * istype T') ->

     (U : (U':texp) * istype U') ->

     (f : (f':oexp) * hastype f' ([∏] T₁ (_ |-> U₁))) ->

     (o : (o':oexp) * hastype o' T₁) ->

     (e: Singleton(([ev] f₁ o₁ (_ |-> U₁)) : oexp)) * hastype e U₁.

Rule 26 ev_eq :: ∏ T : texp, ∏ U : oexp ⟶ texp, ∏ f : oexp, ∏ o : oexp,

     ∏ T' : texp, ∏ U' : oexp ⟶ texp, ∏ f' : oexp, ∏ o' : oexp,

     (∏ x:oexp, [ x : T ] ⟶ [ (U x) = (U' x) ]) ⟶ 

     [ f = f' : ([∏] T U) ] ⟶ 

     [ o = o' : T ] ⟶ 

     [ ([ev] f o U) = ([ev] f' o' U') : (U o)].

Rule 27 beta_reduction :: ∏ T : texp, ∏ U : oexp ⟶ texp, ∏ t : oexp, ∏ f : oexp ⟶ oexp,

     [ t : T ] ⟶ 

     (∏ t':oexp, [ t' : T ] -> [ (f t') : (U t') ]) ⟶

     [ ([ev] ( [λ] T f ) t U) = (f t) : (U t) ].

Rule 28 eta_reduction :: ∏ T:texp, ∏ U:oexp ⟶ texp, ∏ f:oexp,

     [ f : ([∏] T U) ] ⟶ [ ([λ] T (x ⟼ ([ev] f x U))) = f : ([∏] T U) ].

Rule 29 j_type :: ∏ M1:uexp, ∏ M2:uexp, 

     uequal ([max] M1 M2) M2 ⟶ [ ([j] M1 M2) : ([∏] ([U] M1) (_ ⟼ ([U] M2))) ].

Rule 30 El_j_reduction :: ∏ M1:uexp, ∏ M2:uexp, ∏ o:oexp,

     [ o : ([U] M1) ] ⟶ uequal ([max] M1 M2) M2 ⟶ [ ([El]( [ev] ([j] M1 M2) o (_ ⟼ ([U] M2)) )) = ([El] o) ].

Rule 31 forall_type :: ∏ M1:uexp, ∏ M2:uexp, ∏ o1:oexp, ∏ o2:oexp ⟶ oexp,

     ( ∏ x:oexp, [ x : ([El] o1) ] ⟶ [ (o2 x) : ([U] M2) ] ) ⟶

     [ ( [∀] M1 M2 o1 o2 ) : ([U] ( [max] M1 M2 )) ].

Rule 31.2 forall :: 

     (M1:uexp) -> (M2:uexp) ->

     (o1 : (o1:oexp) * [ o1 : ([U] M1) ]) ->

     (o2 : (o2:oexp -> oexp) * ( (x:oexp) -> [ x : ([El] o1_1) ] -> [ (o2 x) : ([U] M2) ] )) ->

     (e : Singleton( ( [∀] M1 M2 o1_1 o2_1 ) : oexp )) * [ e : ([U] ( [max] M1 M2 )) ].

Axiom LFtypeTS forall2 : 

      [ |- M1 Ulevel ] => [ |- M2 Ulevel ] => 

      [ |- o1 : [U](M1) ] =>

      [ x : [El](o1) |- o2 : [U](M2) ] =>

      [ := [∀;x](M1,M2,o1,o2) : [U]([max](M1,M2)) ].

Check LF forall.
Check LF forall2.

Rule 32 El_forall_reduction :: ∏ M1 : uexp, ∏ M2 : uexp, ∏ o1 : oexp, ∏ o2 : oexp ⟶ oexp,

     [ o1 : ([U] M1) ] ⟶

     (∏ x: oexp, [ x : ([El] o1) ] ⟶ [ (o2 x) : ([U] M2) ]) ⟶

     [ ([El] ([∀] M1 M2 o1 o2)) = ([∏] ([El] o1) (x ⟼ ([El] (o2 x)))) ].

Rule 32.1 El_forall :: 

     (M1 : uexp) -> (M2 : uexp) ->

     (o1 : (o1 : oexp) * hastype o1 ([U] M1)) ->

     (o2 : (o2 : oexp -> oexp) * ( (x : (x:oexp) * hastype x ([El] o1_1) ) -> hastype (o2 x_1) ([U] M2))) ->

     tequal ([El] ([∀] M1 M2 o1_1 o2_1)) ([∏] ([El] o1_1) (x ⟼ ([El] (o2_1 x)))) .

Rule 100 teq_empty_eta :: ∏ T:texp, ∏ T':texp, ∏ a:oexp,

     [ a : ([Empty]) ] ⟶ [ T Type ] ⟶ [ T' Type ] ⟶ [ T = T'].

Rule 101 oeq_empty_eta :: ∏ T:texp, ∏ x:oexp, ∏ y:oexp, ∏ a:oexp,

     [ a : ([Empty]) ] ⟶ [ x : T ] ⟶ [ y : T ] ⟶ [ x = y : T ].

Rule 200 jMM_reduction :: ∏ M1:uexp, ∏ M2:uexp,

     uequal M1 M2 ⟶ 

     [ ([j] M1 M2) = ([lambda] ([U](M1)) (x |-> x)) : ([∏] ([U] M1) (_ ⟼ ([U] M2))) ].

Rule 201 jj_reduction :: ∏ M1:uexp, ∏ M2:uexp, ∏ M2':uexp, ∏ M3:uexp, Pi o:oexp,

     uequal M2 M2' ⟶ 

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
