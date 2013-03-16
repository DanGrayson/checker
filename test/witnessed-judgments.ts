Mode TTS.

Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> witnessed_hastype t o p.
Check LF : (p:wexp) -> (t:texp) -> (t':texp) -> witnessed_type_equality t t' p.
Check LF : (p:wexp) -> (t:texp) -> (o:oexp) -> (o':oexp) -> witnessed_object_equality t o o' p.

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
Variable x : T. 

Check TTS : [ T -> @[U] Type ].
Variable f : T -> @[U].
Axiom LF f$ : wexp.
Axiom LF x$ : wexp.

Check TTS : [ _ : f : T -> @[U] ].
Check TTS : [ _ : x : T ].
Check TTS : [ _ : @[ev;_][f,x,T,@[U]] : @[U] ].
Check TTS : [ _ : @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]: @[U]].

# Lemma a1 [ : f : T->@[U] ] ::= f$ .
# Lemma a2 [ : f : T->@[U] ] ::= _ .

Check TTS : [ @[El][@[ev;_][f,x,T,@[U]],@[wev][f$,x$]] Type ].
# Check TTS : [ @[El][@[ev;_][f,x,T,@[U]],@[wev][a1,x$]] Type ].
Check TTS : [ @[El][@[ev;_][f,x,T,@[U]],_] Type ].
Check TTS : [ *@[ev;_][f,x,T,@[U]] Type ].		    # * is notation for El

Check TTS : [ @[Proof][
    @[wev][@[wlam;o][@[wev][f$,o$]],x$],
    @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]],
    @[U]]
  Type ].

Variable A : @[Proof][
    @[wev][@[wlam;o][@[wev][f$,o$]],x$],
    @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]],
    @[U]].

Check TTS : [ *@[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]] Type ].

Check TTS : [
    _ : @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]
      ≡ @[ev;_][@[λ;z][T,@[ev;_][f,z,T,@[U]]],x,T,@[U]]
      : @[U]
      ].

Check TTS : [
    _ : @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]
      ≡ @[ev;_][f,x,T,@[U]]
      : @[U]
      ].

Check TTS : [ 
    _ : @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]
      ≡ @[ev;_][f,x,T,@[U]]
      : @[U]
      ].

# Make head reduction work.
# This one is the same as the one above, with objects reversed.
# Check TTS : [ _
#       : @[ev;_][f,x,T,@[U]]
#       ≡ @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]
#       : @[U]
#       ].

Check TTS : [
    _ : * @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]
      ≡ * @[ev;_][f,x,T,@[U]]
      ].

Check TTS : [
    _ : * @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,T,@[U]]
      ≡ * @[ev;_][f,x,T,@[U]]
      ].

# Check TTS : [ a2 : f : T->@[U] ] .

Check TTS : [
    _ : * @[ev][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,_,_]
      ≡ * @[ev;_][f,x,T,@[U]]
      ].

Check TTS : [
    _ : * @[ev;a][@[λ;y][T,@[ev;_][f,y,T,@[U]]],x,_,_]
      ≡ * @[ev;_][f,x,T,@[U]]
      ].

Check TTS : [
    _ : * @[λ;y][T,f y] x
      ≡ * f x
      ].

Check TTS : [
    _ : * (λ y:T,f y) x
      ≡ * f x
      ].

Check TTS : [
    _ : * ((y:T) |-> f y) x
      ≡ * f x
      ] .

Check TTS : [
    _ : * ((y:T) ⟼ f y) x
      ≡ * f x
      ] .

End. # working on simplifying the syntax for the user

Lemma a8 : * (λ y:T,f y) x ≡ * f x.

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
