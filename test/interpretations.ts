# -*- coding: utf-8 -*-

Include "rules/TS2.ts"..

# derive versions of some inference rules with simple types

Definition pi1 { ⊢ T U Type } ⊢ @∏[T,_.U] Type ::=

   T ⟼ U ⟼ (_, T' ⟼ U' ⟼ (∏_istype T (_ ⟼ U) SND T' (_ ⟼ _ ⟼ U')))..

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ @λ[T,o] : @∏[T,_.U] ::=

   T ⟼ U ⟼ o ⟼ ((@λ T o), T' ⟼ U' ⟼ (λ_hastype T (_ ⟼ U) o SND T' (_ ⟼ _ ⟼ U')))..

Definition ev1 { ⊢ T U Type, f : @∏[T,_.U], o : T } ⊢ @ev[f,o,T,_.U] : U ::=

   T ⟼ U ⟼ f ⟼ o ⟼
   ((ev_hastype T (_ ⟼ U) f o FST), T' ⟼ U' ⟼ (ev_hastype T (_ ⟼ U) f o SND T' (_ ⟼ _ ⟼ U')))..

Theorem compose { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::=
   T ⟼ U ⟼ V ⟼
   ((lambda1 (pi1 T U FST) (pi1 (pi1 U V FST) (pi1 T V FST) FST)
	     (f ⟼ (lambda1 (pi1 U V FST) (pi1 T V FST)
		      (g ⟼ (lambda1 T V
				  (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) FST)) FST)) FST),
   dT ⟼ dU ⟼ dV ⟼
   (lambda1 (pi1 T U FST)
	    (pi1 (pi1 U V FST) (pi1 T V FST) FST)
	    (f ⟼ (lambda1 (pi1 U V FST) (pi1 T V FST)
		      (g ⟼ (lambda1 T V
				  (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) FST)) FST)) SND
	   (pi1 T U SND dT dU)
	   (pi1 (pi1 U V FST) (pi1 T V FST) SND (pi1 U V SND dU dV) (pi1 T V SND dT dV))
	   (f ⟼ df ⟼ (lambda1
		      (pi1 U V FST)
		      (pi1 T V FST)
		      (g ⟼ (lambda1 T V
				  (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) FST)) SND
				       (pi1 U V SND dU dV)
				       (pi1 T V SND dT dV)
		   (g ⟼ dg ⟼ (lambda1 T V
				  (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) SND dT dV
				  (t ⟼ dt ⟼ (ev1 U V g
						 (ev1 T U f t FST) SND
						 dU dV dg
						 (ev1 T U f t SND dT dU df dt)))))))))..

   # Here's what the proof above looks like if we delete all the expression parts, keeping
   # only the judgment parts, from which the expression parts can be deduced.  Then it looks
   # as linear as in the intrinsic encoding..

   # T ⟼ U ⟼ V ⟼
   # (_,
   # dT ⟼ dU ⟼ dV ⟼
   # (lambda1 _ _ _ SND
   # 	   (pi1 _ _ SND dT dU)
   # 	   (pi1 _ _ SND (pi1 _ _ SND dU dV) (pi1 _ _ SND dT dV))
   # 	   (f ⟼ df ⟼ (lambda1 _ _ _ SND
   # 				       (pi1 _ _ SND dU dV)
   # 				       (pi1 _ _ SND dT dV)
   # 		   (g ⟼ dg ⟼ (lambda1 _ _ _ SND dT dV
   # 				  (t ⟼ dt ⟼ (ev1 _ _ g _ SND
   # 						 dU dV dg
   # 						 (ev1 _ _ f t SND dT dU df dt)))))))))..

Theorem compose' { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::=
    # this time with micro-tactics (which don't help in pairs mode!)
    T ⟼ U ⟼ V ⟼
    ((@λ (@∏ T (_ ⟼ U)) (f ⟼ (@λ (@∏ U (_ ⟼ V)) (g ⟼ (@λ T (t ⟼ (@ev g (@ev f t T (_ ⟼ U)) U (_ ⟼ V))))))))
     # (lambda1 (pi1 T U FST) (pi1 (pi1 U V FST) (pi1 T V FST) FST)
     # 	          (f ⟼ (lambda1 (pi1 U V FST) (pi1 T V FST)
     # 			   (g ⟼ (lambda1 T V
     # 			   	       (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) FST)) FST)) FST)
											       ,
    _ ⟼ _ ⟼ _ ⟼
    (λ_hastype (pi1 T U FST)
	 (_ ⟼ (pi1 (pi1 U V FST) (pi1 T V FST) FST))
	 (f ⟼ (λ_hastype (pi1 U V FST) (_ ⟼ (pi1 T V FST))
		   (g ⟼ (λ_hastype T (_ ⟼ V)
			       (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) FST)) FST)) SND
	(pi1 T U SND _ _)
	(_ ⟼ _ ⟼ (pi1 (pi1 U V FST) (pi1 T V FST) SND (pi1 U V SND _ _) (pi1 T V SND _ _)))
	(f ⟼ _ ⟼ (λ_hastype
	       (pi1 U V FST)
	       (_ ⟼ (pi1 T V FST))
	       (g ⟼ (λ_hastype T (_ ⟼ V)
			   (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) FST)) SND
				(pi1 U V SND _ _)
				(_ ⟼ _ ⟼ (∏_istype T (_ ⟼ V) SND _ _))
	       (g ⟼ _ ⟼ (λ_hastype T (_ ⟼ V)
			      (t ⟼ (ev1 U V g (ev1 T U f t FST) FST)) SND _ _
			       (t ⟼ _ ⟼ (ev1 U V g (ev1 T U f t FST) SND
					      _ _ _ (ev1 T U f t SND _ _ _ _)))))))))..

  # ev1 : (T:texp) ⟶
  #       (U:texp) ⟶
  #       (f:oexp) ⟶
  #       (o:oexp) ⟶
  #       (x:Singleton((@ev f o (_ ⟼ U)) : oexp)) ×
  #         istype T ⟶
  #         istype U ⟶
  #         hastype f (@∏ T (_ ⟼ U)) ⟶
  #         hastype o T ⟶
  #         hastype x U

Definition barbara { |- T U V Type } ⊢ (T->U) -> (U->V) -> (T->V) Type ::=
    T ⟼ U ⟼ V ⟼ (_, $tscheck )..

    # working on $tscheck

# Theorem compose'' { |- T U V Type } : (T->U) -> (U->V) -> (T->V) ::=
#     T ⟼ U ⟼ V ⟼ (
#      (@λ (@∏ T (_ ⟼ U)) (f ⟼ (@λ (@∏ U (_ ⟼ V)) (g ⟼ (@λ T (t ⟼ (@ev g (@ev f t T (_ ⟼ U)) U (_ ⟼ V)))))))),
#      _ ⟼ _ ⟼ _ ⟼ $tscheck
#      )..

#   Local Variables:
#   compile-command: "make -C .. interpretations DEBUG=no"
#   End:
