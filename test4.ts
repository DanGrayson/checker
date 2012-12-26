# judged expression level

Axiom LF Pi_istype' : (T:a_type) -> ( obj_of_type T -> a_type ) -> a_type.

Axiom LF U_istype' : uexp -> a_type.

Axiom LF u_hastype' : (M:uexp) -> obj_of_type (U_istype' ([next](M))).

Axiom LF El_istype' : (M:uexp) -> obj_of_type (U_istype' M) -> a_type.

Axiom LF El_u_reduction' : (M:uexp) -> judged_type_equal (El_istype' M (u_hastype' M)) (U_istype' M).

Axiom LF lambda_hastype' : (T:a_type) -> (U : obj_of_type T -> a_type) -> (body : (t:obj_of_type T) -> obj_of_type (U t)) 

      			    -> obj_of_type (Pi_istype' T U).

Axiom LF ev_hastype' : (T:a_type) -> (U : obj_of_type T -> a_type) -> (f : obj_of_type (Pi_istype' T U)) -> (o : obj_of_type T)

		       -> obj_of_type (U o).

Axiom LF beta_reduction' : (T:a_type) -> (o1 : obj_of_type T) -> (U : obj_of_type T -> a_type) -> (o2 : (t:obj_of_type T) -> obj_of_type (U t)) 

			   -> judged_obj_equal (U o1) (ev_hastype' T U (lambda_hastype' T U o2) o1) (o2 o1).

Show.

#   Local Variables:
#   compile-command: "make run4 "
#   End:
