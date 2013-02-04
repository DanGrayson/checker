Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> w_hastype p o t.
Check LF : (p:wexp) -> (t:texp) -> (t':texp) -> w_type_equality p t t'.
Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> (o':oexp) -> w_object_equality p o o' t.

Axiom LF p : wexp.
Axiom LF T : texp.
Axiom LF T' : texp.
Axiom LF o : oexp.
Axiom LF o' : oexp.
Check TS : [ p : o : T ].
Check TS : [ p : T ≡ T' ].
Check TS : [ p : o ≡ o' : T ].

Variable W Type.
Check TTS : [ @[U'] Type ].
Variable xo : T.				      # Eventually we'll be checking that the type
Check TTS : [ @[Pi';_][T,@[U']] Type ].
Variable xf : @[Pi';_][T,@[U']].			      # to the right of the colon is valid here.
Axiom LF xf$ : wexp.
Axiom LF xo$ : wexp.
Check TTS : [ _ : xf : @[Pi';_][T,@[U']] ].
Check TTS : [ _ : xo : T ].
Check TTS : [ _ : @[ev';_][xf,xo,T,@[U']] : @[U'] ].
Check TTS : [ @[El'][@[ev';_][xf,xo,T,@[U']],_] Type ].
End.							    # working on tactic $witness
Check TTS : [ 
    _ :
    @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']]:
    @[U']].
End.							    # working on tactic $witness
Check TTS : [ 
    @[wev][@[wlam;o][@[wev][xf$,o$]],xo$]:
    @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']]:
    @[U']].

Check TTS : [ @[Proof][ 
    @[wev][@[wlam;o][@[wev][xf$,o$]],xo$],
    @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']],
    @[U']] 
  Type ].

Variable A : @[Proof][ 
    @[wev][@[wlam;o][@[wev][xf$,o$]],xo$],
    @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']],
    @[U']].

Show 1.

Check TTS : [ 
  @[El'][
    @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']],
    @[wev][@[wlam;o][@[wev][xf$,o$]],xo$]
  ] Type ].

# working on definitions:

# Check TTS : [ @[El'][A,A$] Type ].

Check TTS : [ 
        @[wbeta;y][xo$,@[wev][xf$,y$]]
      : @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']]
      ≡ @[ev';_][xf,xo,T,@[U']]
      : @[U']
      ].

Check TTS : [ 
        @[weleq][ @[wbeta;y][xo$,@[wev][xf$,y$]] ]
      : @[El'][ @[ev';_][@[λ';y][T,@[ev';_][xf,y,T,@[U']]],xo,T,@[U']],
		@[wev][@[wlam;o][@[wev][xf$,o$]],xo$]]
      ≡ @[El'][ @[ev';_][xf,xo,T,@[U']],
      		@[wev][xf$,xo$]]
      ].

End.							    # working on the witness checker

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
