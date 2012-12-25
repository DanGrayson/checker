# Show.

# Check : TS { |- T Type } { x:T |- U Type } { |- b : T } oexp.

Axiom 3.4.17 El { ⊢ M Ulevel, o : [U](M) } ⊢ *o Type.

Check LF El.

Check : TS { |- T Type } Type.

# Check : LF (U : (T:texp) ** istype T) -> istype U_1.


End.

#   Local Variables:
#   compile-command: "make run2 "
#   End:
