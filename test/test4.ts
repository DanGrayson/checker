# new "judged expression" level:

Axiom LF pi : (T:type) ⟶ ( obj_of_type T ⟶ type ) ⟶ type.

Axiom LF UU : uexp ⟶ type.

Axiom LF uu : (M:uexp) ⟶ obj_of_type (UU ([next] M)).

Axiom LF El : (M:uexp) ⟶ obj_of_type (UU M) ⟶ type.

Axiom LF El_u_reduction : (M:uexp) ⟶ type_equality (El M (uu M)) (UU M).

Axiom LF cast : (T:type) ⟶ (U:type) ⟶ type_equality T U ⟶ obj_of_type T ⟶ obj_of_type U.

Axiom LF forall : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (UU M1)) ⟶ (o2 : obj_of_type (El M1 o1) ⟶ obj_of_type (UU M2)) 
      		   ⟶ obj_of_type (UU ([max] M1 M2)).

Axiom LF lamb : (T:type) ⟶ 
      		(U : obj_of_type T ⟶ type) ⟶ 
		(body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
	   ⟶ obj_of_type (pi T U).

Axiom LF ev : (T:type) ⟶ 
      	      (U : obj_of_type T ⟶ type) ⟶ 
	      (f : obj_of_type (pi T U)) ⟶ 
	      (arg : obj_of_type T) 
	   ⟶ obj_of_type (U arg).

Axiom LF beta_reduction : (T:type) ⟶ 
      			  (arg : obj_of_type T) ⟶ 
			  (U : obj_of_type T ⟶ type) ⟶ 
			  (body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
             ⟶ object_equality (U arg) (ev T U (lamb T U body) arg) (body arg).

Theorem LF id0 : (T:type) ⟶ (t:obj_of_type T) ⟶ obj_of_type T := _ ⟼ t ⟼ t.

Theorem LF id0' : (u:uexp) ⟶ (T:obj_of_type (UU u)) ⟶ (t:obj_of_type (El u T)) ⟶ obj_of_type (El u T) := _ ⟼ _ ⟼ t ⟼ t.

Theorem LF id3' : (u:uexp) ⟶ (T:obj_of_type (UU u)) ⟶ (T':obj_of_type (UU u)) ⟶ (f:obj_of_type (pi (El u T) (_ ⟼ (El u T'))))
			   ⟶ (t:obj_of_type (El u T)) ⟶ obj_of_type (El u T') :=
	u ⟼ T ⟼ T' ⟼ (ev (El u T) (_ ⟼ (El u T'))).

Theorem LF make : (T:type) ⟶ (U:type) ⟶ (f : obj_of_type T ⟶ obj_of_type U) ⟶ obj_of_type (pi T (_ ⟼ U)) := 
	T ⟼ U ⟼ (lamb T (_ ⟼ U)).

# introduce non-dependent versions of pi, lamb, and ev:

Definition LF arrow : (T:type) ⟶ (U:type) ⟶ type := T ⟼ U ⟼ (pi T (_ ⟼ U)).

Definition LF lamb1 : (T:type) ⟶ (U:type) ⟶ (body : (t:obj_of_type T) ⟶ obj_of_type U) ⟶ obj_of_type (arrow T U) :=
	   T ⟼ U ⟼ (lamb T (_ ⟼ U)).

Definition LF ev1 : (T:type) ⟶ (U:type) ⟶ (f : obj_of_type (arrow T U)) ⟶ (arg : obj_of_type T) ⟶ obj_of_type U :=
	   T ⟼ U ⟼ (ev T (_ ⟼ U)).

Theorem LF modus_ponens : (T:type) ⟶ (U:type) ⟶ (V:type) ⟶ obj_of_type (arrow (arrow T U) (arrow (arrow U V) (arrow T V))) :=
	T ⟼ U ⟼ V ⟼ 
	(lamb1 (arrow T U)
	       (arrow (arrow U V) (arrow T V))
	       (f ⟼ (lamb1 (arrow U V)
	       		   (arrow T V)
			   (g ⟼ (lamb1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t)))))))).

Axiom LF El_forall_reduction : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (UU M1))
      	⟶ (o2 : obj_of_type (El M1 o1) ⟶ obj_of_type (UU M2)) 
	⟶ type_equality (El ([max] M1 M2) (forall M1 M2 o1 o2)) (pi (El M1 o1) (x ⟼ (El ([max] M1 M2) (o2 x)))).

Lemma LF A : (u:uexp) ⟶ (T : obj_of_type (UU u)) ⟶ (U : obj_of_type (UU u))
		      ⟶ (f : obj_of_type (El u (forall u u T (_ ⟼ U))))
		      ⟶ obj_of_type (pi (El u T) (_ ⟼ (El u U))) :=
                 u ⟼ T ⟼ U ⟼ 
		 (cast (El u (forall u u T (_ ⟼ U))) 
                       (pi (El u T) (_ ⟼ (El u U)))
                       (El_forall_reduction u u T (_ ⟼ U))).

Theorem LF compose3 : (u:uexp) ⟶ (T : obj_of_type (UU u)) ⟶ (U : obj_of_type (UU u)) ⟶ (V : obj_of_type (UU u)) ⟶ 
		      (g : obj_of_type (El u (forall u u U (_ ⟼ V)))) ⟶
		      (f : obj_of_type (El u (forall u u T (_ ⟼ U)))) ⟶
		      (t : obj_of_type (El u T)) ⟶
		      obj_of_type (El u V) := 
                 u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
		      (ev (El u U) (_ ⟼ (El u V)) (A u U V g) (ev (El u T) (_ ⟼ (El u U)) (A u T U f) t)) .

#   Local Variables:
#   compile-command: "make -C .. run4 "
#   End:
