# -*- coding: utf-8 -*-

# Here we translate the file ../NOTES/ts.elf into our syntax.

Axiom LF istype_Empty : istype @[Empty].

Axiom LF istype_Forall : (T1:texp) ⟶ (T2:oexp⟶texp) ⟶ 
      ((x:oexp) ⟶ hastype x T1 ⟶ istype (T2 x)) ⟶ istype (@[Pi] T1 T2).

Axiom LF hastype_lambda : (T1:texp) ⟶ (T2:oexp⟶texp) ⟶ (O:oexp⟶oexp) ⟶ 
      ((x:oexp) ⟶ hastype x T1 ⟶ hastype (O x) (T2 x)) ⟶ 
      hastype (@[lambda] T1 O) (@[Pi] T1 T2).

Axiom LF hastype_ev : (T1:texp) ⟶ (T2:oexp⟶texp) ⟶ (F:oexp) ⟶ (O:oexp) ⟶ 
      hastype O T1 ⟶ hastype F (@[Pi] T1 T2) ⟶ hastype (@[ev] F O T2) (T2 O).

Axiom LF hastype_empty_r : (O:oexp) ⟶ (T:texp) ⟶ hastype O @[Empty] ⟶ 
      istype T ⟶ hastype (@[empty_r] T O) T.

Axiom LF hastype_eq : (T1:texp) ⟶ (T2:texp) ⟶ (O:oexp) ⟶ tequal T1 T2 ⟶ 
      hastype O T2 ⟶ hastype O T1.

Axiom LF o_eq_beta : (T1:texp) ⟶ (T2:oexp⟶texp) ⟶ (O1:oexp) ⟶ (O2:oexp⟶oexp) ⟶
      (x:oexp) ⟶ hastype x T1 ⟶ hastype (O2 x) (T2 x) ⟶
      hastype O1 T1 ⟶
      oequal (@[ev] (@[lambda] T1 O2) O1 T2) (O2 O1) (T2 O1).

Axiom LF o_eq_app : (T1:texp) ⟶ (T2:oexp⟶texp) ⟶ (O:oexp) ⟶ (O':oexp) ⟶ 
      (F:oexp) ⟶ (F':oexp) ⟶ 
      oequal O O' T1 ⟶ oequal F F' (@[Pi] T1 T2) ⟶
      oequal (@[ev] F O T2) (@[ev] F' O' T2) (T2 O).

Axiom LF o_eq_empty_eta : (O:oexp) ⟶ (O1:oexp) ⟶ (O2:oexp) ⟶ (A:texp) ⟶ 
      hastype O @[Empty] ⟶ hastype O1 A ⟶ hastype O2 A ⟶ oequal O1 O2 A.

Axiom LF t_eq_empty_eta : (O:oexp) ⟶ (B:texp) ⟶ (A:texp) ⟶ 
      hastype O @[Empty] ⟶ istype B ⟶ istype A ⟶ tequal A B.

Theorem LF foo : (T1:texp) ⟶ (T2:texp) ⟶ (T3:texp) ⟶ (F:oexp) ⟶ (O:oexp) ⟶ (Bad:oexp) ⟶
      istype T1 ⟶ istype T2 ⟶ hastype O T1 ⟶ hastype F (@[Pi] T2 (_ ⟼ T3)) ⟶
      hastype Bad @[Empty] ⟶ hastype (@[ev] F O (_ ⟼ T3)) T3 
      :=
      T1 ⟼ T2 ⟼ T3 ⟼ F ⟼ O ⟼ Bad ⟼ dT1 ⟼ dT2 ⟼ dO ⟼ dF ⟼ dBad ⟼ 
      (hastype_ev T2 (_ ⟼ T3) F O 
          (hastype_eq T2 T1 O (t_eq_empty_eta Bad T1 T2 dBad dT1 dT2) dO) dF).

# this time with tactics:
Theorem LF foo' : (T1:texp) ⟶ (T2:texp) ⟶ (T3:texp) ⟶ (F:oexp) ⟶ (O:oexp) ⟶ (Bad:oexp) ⟶
      istype T1 ⟶ istype T2 ⟶ hastype O T1 ⟶ hastype F (@[Pi] T2 (_ ⟼ T3)) ⟶
      hastype Bad @[Empty] ⟶ hastype (@[ev] F O (_ ⟼ T3)) T3 
      :=
      T1 ⟼ T2 ⟼ T3 ⟼ F ⟼ O ⟼ Bad ⟼ dT1 ⟼ dT2 ⟼ dO ⟼ dF ⟼ dBad ⟼ 
      (hastype_ev T2 (_ ⟼ T3) F O 
      	  (hastype_eq T2 T1 O (t_eq_empty_eta Bad T1 T2 _ _ _) _) _).

Show 20.

#   Local Variables:
#   compile-command: "make -C .. ts-elf "
#   End:
