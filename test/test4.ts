# -*- coding: utf-8 -*-

# new "judged expression" level:

Axiom LF ∏_istype : (T:a_type) ⟶ ( obj_of_type T ⟶ a_type ) ⟶ a_type.

Axiom LF UU : uexp ⟶ a_type.

Axiom LF uu : (M:uexp) ⟶ obj_of_type (UU (@[next] M)).

Axiom LF El : (M:uexp) ⟶ obj_of_type (UU M) ⟶ a_type.

Axiom LF El_u_reduction : (M:uexp) ⟶ type_equality (El M (uu M)) (UU M).

Axiom LF cast : (T:a_type) ⟶ (U:a_type) ⟶ type_equality T U ⟶ obj_of_type T ⟶ obj_of_type U.

Axiom LF forall : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (UU M1)) ⟶ (o2 : obj_of_type (El M1 o1) ⟶ obj_of_type (UU M2)) 
      		   ⟶ obj_of_type (UU (@[max] M1 M2)).

Axiom LF lamb : (T:a_type) ⟶ 
      		(U : obj_of_type T ⟶ a_type) ⟶ 
		(body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
	   ⟶ obj_of_type (∏_istype T U).

Axiom LF ev : (T:a_type) ⟶ 
      	      (U : obj_of_type T ⟶ a_type) ⟶ 
	      (f : obj_of_type (∏_istype T U)) ⟶ 
	      (arg : obj_of_type T) 
	   ⟶ obj_of_type (U arg).

Axiom LF beta_reduction : (T:a_type) ⟶ 
      			  (arg : obj_of_type T) ⟶ 
			  (U : obj_of_type T ⟶ a_type) ⟶ 
			  (body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
             ⟶ object_equality (U arg) (ev T U (lamb T U body) arg) (body arg).

Theorem LF id0 : (T:a_type) ⟶ (t:obj_of_type T) ⟶ obj_of_type T := _ ⟼ t ⟼ t.

Theorem LF id0' : (u:uexp) ⟶ (T:obj_of_type (UU u)) ⟶ (t:obj_of_type (El u T)) ⟶ obj_of_type (El u T) := _ ⟼ _ ⟼ t ⟼ t.

Theorem LF id3' : (u:uexp) ⟶ (T:obj_of_type (UU u)) ⟶ (T':obj_of_type (UU u)) ⟶ (f:obj_of_type (∏_istype (El u T) (_ ⟼ (El u T'))))
			   ⟶ (t:obj_of_type (El u T)) ⟶ obj_of_type (El u T') :=
	u ⟼ T ⟼ T' ⟼ (ev (El u T) (_ ⟼ (El u T'))).

Theorem LF make : (T:a_type) ⟶ (U:a_type) ⟶ (f : obj_of_type T ⟶ obj_of_type U) ⟶ obj_of_type (∏_istype T (_ ⟼ U)) := 
	T ⟼ U ⟼ (lamb T (_ ⟼ U)).

# introduce non-dependent versions of ∏_istype, lamb, and ev:

Definition LF pi1 : (T:a_type) ⟶ (U:a_type) ⟶ a_type := T ⟼ U ⟼ (∏_istype T (_ ⟼ U)).

Definition LF lamb1 : (T:a_type) ⟶ (U:a_type) ⟶ (body : (t:obj_of_type T) ⟶ obj_of_type U) ⟶ obj_of_type (pi1 T U) :=
	   T ⟼ U ⟼ (lamb T (_ ⟼ U)).

Definition LF ev1 : (T:a_type) ⟶ (U:a_type) ⟶ (f : obj_of_type (pi1 T U)) ⟶ (arg : obj_of_type T) ⟶ obj_of_type U :=
	   T ⟼ U ⟼ (ev T (_ ⟼ U)).

Theorem LF modus_ponens : (T:a_type) ⟶ (U:a_type) ⟶ (V:a_type) ⟶ obj_of_type (pi1 (pi1 T U) (pi1 (pi1 U V) (pi1 T V))) :=
	T ⟼ U ⟼ V ⟼ 
	(lamb1 (pi1 T U)
	       (pi1 (pi1 U V) (pi1 T V))
	       (f ⟼ (lamb1 (pi1 U V)
	       		   (pi1 T V)
			   (g ⟼ (lamb1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t)))))))).

Axiom LF El_forall_reduction : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (UU M1))
      	⟶ (o2 : obj_of_type (El M1 o1) ⟶ obj_of_type (UU M2)) 
	⟶ type_equality (El (@[max] M1 M2) (forall M1 M2 o1 o2)) (∏_istype (El M1 o1) (x ⟼ (El (@[max] M1 M2) (o2 x)))).

Lemma LF A : (u:uexp) ⟶ (T : obj_of_type (UU u)) ⟶ (U : obj_of_type (UU u))
		      ⟶ (f : obj_of_type (El u (forall u u T (_ ⟼ U))))
		      ⟶ obj_of_type (∏_istype (El u T) (_ ⟼ (El u U))) :=
                 u ⟼ T ⟼ U ⟼ 
		 (cast (El u (forall u u T (_ ⟼ U))) 
                       (∏_istype (El u T) (_ ⟼ (El u U)))
                       (El_forall_reduction u u T (_ ⟼ U))).

Theorem LF compose3 : (u:uexp) ⟶ (T : obj_of_type (UU u)) ⟶ (U : obj_of_type (UU u)) ⟶ (V : obj_of_type (UU u)) ⟶ 
		      (g : obj_of_type (El u (forall u u U (_ ⟼ V)))) ⟶
		      (f : obj_of_type (El u (forall u u T (_ ⟼ U)))) ⟶
		      (t : obj_of_type (El u T)) ⟶
		      obj_of_type (El u V) := 
                 u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
		      (ev (El u U) (_ ⟼ (El u V)) (A u U V g) (ev (El u T) (_ ⟼ (El u U)) (A u T U f) t)) .

#   Local Variables:
#   compile-command: "make -C .. test4 "
#   End:
