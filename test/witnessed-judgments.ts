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

Axiom LF u : uexp.
Variable T Type.
Variable xo : T.				      # Eventually we'll be checking that the type
Variable xf : T -> @[U][u].			      # to the right of the colon is valid here.
Show.

Check TS Witness : [ @[wd_2] : xf : T -> @[U][u] ].
Check TS Witness : [ @[wd_1] : xo : T ].
Check TS Witness : [ @[wev][@[wd_2],@[wd_1]] : @[ev;_][xf,xo,T,@[U][u]] : @[U][u] ].

Check TS Witness : [ @[wlam;_][@[wev][@[wd_2],@[wd_3]]] : @[λ;y][T,@[ev;_][xf,y,T,@[U][u]]] : T -> @[U][u] ].

# End.							    # working on the witness checker
End.							    # working on the witness checker

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
