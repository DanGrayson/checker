Mode TTS.

Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> witnessed_hastype p o t.
Check LF : (p:wexp) -> (t:texp) -> (t':texp) -> witnessed_type_equality p t t'.
Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> (o':oexp) -> witnessed_object_equality p o o' t.

Axiom LF p : wexp.
Variable T Type.
# Axiom LF T : texp.
Axiom LF T' : texp.
Axiom LF o : oexp.
Axiom LF o' : oexp.
Check TS : [ p : o : T ].
Check TS : [ p : T ≡ T' ].
Check TS : [ p : o ≡ o' : T ].

Variable W Type.
Check TTS : [ @[U] Type ].
Variable xo : T. 

Check TTS : [ T -> @[U] Type ].
Variable xf : T -> @[U].
Axiom LF xf$ : wexp.
Axiom LF xo$ : wexp.
Show.
Check TTS : [ _ : xf : T -> @[U] ].
Check TTS : [ _ : xo : T ].
Check TTS : [ _ : @[ev;_][xf,xo,T,@[U]] : @[U] ].
Check TTS : [ _ : @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]: @[U]].

Lemma a1 [ : xf : T->@[U] ] ::= xf$ .
Lemma a2 [ : xf : T->@[U] ] ::= _ .
Check TTS : [ @[El][@[ev;_][xf,xo,T,@[U]],@[wev][xf$,xo$]] Type ].
Check TTS : [ @[El][@[ev;_][xf,xo,T,@[U]],@[wev][a1,xo$]] Type ].
Check TTS : [ @[El][@[ev;_][xf,xo,T,@[U]],_] Type ].
Check TTS : [ *@[ev;_][xf,xo,T,@[U]] Type ].		    # * is notation for El

Check TTS : [ @[Proof][
    @[wev][@[wlam;o][@[wev][xf$,o$]],xo$],
    @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]],
    @[U]]
  Type ].

Variable A : @[Proof][
    @[wev][@[wlam;o][@[wev][xf$,o$]],xo$],
    @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]],
    @[U]].

Check TTS : [ *@[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]] Type ].

Check TTS : [
    _ : @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]
      ≡ @[ev;_][@[λ;z][T,@[ev;_][xf,z,T,@[U]]],xo,T,@[U]]
      : @[U]
      ].

Check TTS : [
    _ : @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]
      ≡ @[ev;_][xf,xo,T,@[U]]
      : @[U]
      ].

Lemma a4 [
      : @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]
      ≡ @[ev;_][xf,xo,T,@[U]]
      : @[U]
      ] := _.

# Make head reduction work.
# This one is the same as the one above, with objects reversed.
# Check TTS : [ _
#       : @[ev;_][xf,xo,T,@[U]]
#       ≡ @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]
#       : @[U]
#       ].

Check TTS : [
    _ : * @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]
      ≡ * @[ev;_][xf,xo,T,@[U]]
      ].

Lemma a3 [
      : * @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,@[U]]
      ≡ * @[ev;_][xf,xo,T,@[U]]
      ] := _ .

Check LF a3.

Lemma a2a [ : xf : T->@[U] ] := a2 .

End. # working on simplifying the syntax for the user

Lemma a4 [
      : * @[ev;_][@[λ;y][T,@[ev;_][xf,y,T,@[U]]],xo,T,_]
      ≡ * @[ev;_][xf,xo,T,@[U]]
      ] := _ .

# Check TTS : [ @[El][A,A$] Type ].

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
