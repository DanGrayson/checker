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

Variable W Type.
Check TS Witness : [ @[U'] Type ].
Variable xo : T.				      # Eventually we'll be checking that the type
Check TS Witness : [ T -> @[U'] Type ].
Variable xf : T -> @[U'].			      # to the right of the colon is valid here.
Show.
Check TS Witness : [ @[wd_2] : xf : T -> @[U'] ].
Check TS Witness : [ @[wd_1] : xo : T ].
Check TS Witness : [ @[wev][@[wd_2],@[wd_1]] : @[ev;_][xf,xo,T,@[U']] : @[U'] ].
Check TS Witness : [ @[El'][@[ev;_][xf,xo,T,@[U']],@[wev][@[wd_2],@[wd_1]]] Type ].

Check TS Witness : [ 
      @[wev][ @[wlam;_][@[wev][ @[wd_2],@[wd_3]]],           @[wd_1]] : 
      @[ev;_][@[λ;y][T, @[ev;_][xf,     y,        T,@[U']]], xo,    T,@[U']] : 
      @[U'] ].

End.							    # working on the witness checker

Check TS Witness : [ 
      @[wbeta;_][@[wd_1],@[wev][@[wd_2],@[wd_1]]]
      : @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U']]],xo,T,@[U']]
      ≡ @[ev;_][xf,xo,T,@[U']]
      : @[U']
      ].

End.							    # working on the witness checker

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
