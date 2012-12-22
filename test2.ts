Check : TS { |- T Type } { x:T |- U Type } { |- b : T } oexp.

Check : LF (x:oexp) -> (T:texp) -> hastype x T.
Check : LF (x:oexp) ** (T:texp) -> hastype x T.  # surprising syntax
Check : LF (U : (T:texp) ** istype T) -> istype U_1.


End.

#   Local Variables:
#   compile-command: "make run2 "
#   End:
