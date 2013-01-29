Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> witnessed_hastype p o t.
Check LF : (p:wexp) -> (t:texp) -> (t':texp) -> witnessed_type_equality p t t'.
Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> (o':oexp) -> witnessed_object_equality p o o' t.

Axiom LF p : wexp.
Axiom LF T : texp.
Axiom LF T' : texp.
Axiom LF o : oexp.
Axiom LF o' : oexp.
Check TS : [ p : o : T ].
Check TS : [ p : T ≡ T' ].
Check TS : [ p : o ≡ o' : T ].

Variable T U Type.
Variable xo : T.					    # Eventually we'll be checking that the type
Variable xf : T -> U.					    # to the right of the colon is valid here.
Show.

Check TS Witness : [ @[wd_3] : xf : T -> U ].
Check TS Witness : [ @[wd_2] : xo : T ].
End.							    # working on the witness checker
Check TS Witness : [ @[wev][@[wd_3],@[wd_2]] : @[ev';_][xf,xo,T,U] : U ].

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
