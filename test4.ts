# new "judged expression" level:

Axiom LF pi : (T:type) ⟶ ( obj_of_type T ⟶ type ) ⟶ type.

Axiom LF U : uexp ⟶ type.

Axiom LF u : (M:uexp) ⟶ obj_of_type (U ([next] M)).

Axiom LF El : (M:uexp) ⟶ obj_of_type (U M) ⟶ type.

Axiom LF El_u_reduction : (M:uexp) ⟶ type_equality (El M (u M)) (U M).

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

Theorem LF id0' : (u:uexp) ⟶ (T:obj_of_type (U u)) ⟶ (t:obj_of_type (El u T)) ⟶ obj_of_type (El u T) := _ ⟼ _ ⟼ t ⟼ t.

Theorem LF id3' : (u:uexp) ⟶ (T:obj_of_type (U u)) ⟶ (T':obj_of_type (U u)) ⟶ (f:obj_of_type (pi (El u T) (_ ⟼ (El u T'))))
			   ⟶ (t:obj_of_type (El u T)) ⟶ obj_of_type (El u T') :=
		u ⟼ T ⟼ T' ⟼ f ⟼ t ⟼ (ev (El u T) (_ ⟼ (El u T')) f t).

Theorem LF make : (T:type) ⟶ (U:type) ⟶ (f : obj_of_type T ⟶ obj_of_type U) ⟶ obj_of_type (pi T (_ ⟼ U)) := 
 		T ⟼ U ⟼ f ⟼ (lamb T (_ ⟼ U) f ).

# introduce non-dependent versions of pi, lamb, and ev:

Definition LF arrow : (T:type) ⟶ (U:type) ⟶ type := T ⟼ U ⟼ (pi T (_ ⟼ U)).

Definition LF lamb1 : (T:type) ⟶ (U:type) ⟶ (body : (t:obj_of_type T) ⟶ obj_of_type U) ⟶ obj_of_type (arrow T U) :=
	   T ⟼ U ⟼ body ⟼ (lamb T (_ ⟼ U) body).

Definition LF ev1 : (T:type) ⟶ (U:type) ⟶ (f : obj_of_type (arrow T U)) ⟶ (arg : obj_of_type T) ⟶ obj_of_type U :=
	   T ⟼ U ⟼ f ⟼ arg ⟼ (ev T (_ ⟼ U) f arg).

Theorem LF modus_ponens : (T:type) ⟶ (U:type) ⟶ (V:type) ⟶ obj_of_type (arrow (arrow T U) (arrow (arrow U V) (arrow T V))) :=
	T ⟼ U ⟼ V ⟼ 
	(lamb1 (arrow T U)
	       (arrow (arrow U V) (arrow T V))
	       (f ⟼ (lamb1 (arrow U V)
	       		   (arrow T V)
			   (g ⟼ (lamb1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t)))))))).

#   Local Variables:
#   compile-command: "make run4 "
#   End:
