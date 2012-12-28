# Show.

# Check : TS { |- T Type } { x:T |- U Type } { |- b : T } oexp.

Axiom 3.4.17 El_istype { ⊢ M Ulevel, o : [U](M) } ⊢ *o Type.

Check LF El_istype.

Check : TS { |- T Type } Type.

# Check : LF (U : (T:texp) ** istype T) -> istype U_1.


End.

#   Local Variables:
#   compile-command: "make -C .. run2 "
#   End:
