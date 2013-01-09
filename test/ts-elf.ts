# Here we translate the file ../NOTES/ts.elf into our syntax.

Axiom LF istype_Empty : istype @[Empty].
Axiom LF istype_Forall : (T1:texp) -> (T2:oexp->texp) -> ((x:oexp) -> hastype x T1 -> istype (T2 x)) -> istype (@[Pi] T1 T2).
Axiom LF hastype_lambda : (T1:texp) -> (T2:oexp->texp) -> (O:oexp->oexp) -> ((x:oexp) -> hastype x T1 -> hastype (O x) (T2 x)) -> hastype (@[lambda] T1 O) (@[Pi] T1 T2).
Axiom LF hastype_ev : (T1:texp) -> (T2:oexp->texp) -> (F:oexp) -> (O:oexp) -> hastype O T1 -> hastype F (@[Pi] T1 T2) -> hastype (@[ev] F O T2) (T2 O).
Axiom LF hastype_empty_r : (O:oexp) -> (T:texp) -> hastype O @[Empty] -> istype T -> hastype (@[empty_r] T O) T.
Axiom LF hastype_eq : (T1:texp) -> (T2:texp) -> (O:oexp) -> tequal T1 T2 -> hastype O T2 -> hastype O T1.
Axiom LF o_eq_beta : (T1:texp) -> (T2:oexp->texp) -> (O1:oexp) -> (O2:oexp->oexp) ->
      		((x:oexp) -> hastype x T1 -> hastype (O2 x) (T2 x)) ->
		hastype O1 T1 ->
		oequal (@[ev] (@[lambda] T1 O2) O1 T2) (O2 O1) (T2 O1).
Axiom LF o_eq_app : (T1:texp) -> (T2:oexp->texp) -> (O:oexp) -> (O':oexp) -> (F:oexp) -> (F':oexp) -> 
      		oequal O O' T1 -> oequal F F' (@[Pi] T1 T2) ->
		oequal (@[ev] F O T2) (@[ev] F' O' T2) (T2 O).
Axiom LF o_eq_empty_eta : (O:oexp) -> (O1:oexp) -> (O2:oexp) -> (A:texp) -> 
      		hastype O @[Empty] -> hastype O1 A -> hastype O2 A -> oequal O1 O2 A.
Axiom LF t_eq_empty_eta : (O:oexp) -> (A:texp) -> (B:texp) -> 
            	istype A -> istype B -> hastype O @[Empty] -> tequal A B.

End.

Theorem LF foo (T1:texp) -> (T2:texp) -> (T3:texp) -> (F:oexp) -> (O:oexp)

Show 20.

#   Local Variables:
#   compile-command: "make -C .. ts-elf "
#   End:
