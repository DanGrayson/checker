Mode TTS;;

Variable T Type;;
Variable x : T;;
Variable f : T -> @U;;

Goal [ T -> @U Type ];;

Goal [ f : T -> @U ];;

Goal [ x : T ];;

Goal [ @ev[f,x,T,.@U] : @U ];;

Goal [ @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] : @U ];;

Lemma a [ @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] : @U ];;
Check a;;

Goal [ @El[@ev[f,x,T,.@U]] Type ];;

Goal [ *@ev[f,x,T,.@U] Type ];;		    # * is notation for El

Goal [ *@ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] Type ];;

Goal [ ? : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[@λ[T,z.@ev[f,z,T,.@U]],x,T,.@U] : @U ];;

Goal [ ? : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[f,x,T,.@U] : @U ];;

Goal [ ? : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[f,x,T,.@U] : @U ];;

Goal [ ? : * @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ * @ev[f,x,T,.@U] ];;

Goal [ ? : * @λ[T,y.f y] x ≡ * f x ];;

Goal [ ? : * (λ y:T,f y) x ≡ * f x ];;

Goal [ ? : * ((y:T) |-> f y) x ≡ * f x ];;

Goal [ ? : * ((y:T) ⟼ f y) x ≡ * f x ];;

Lemma a8 [ ? : * (λ y:T,f y) x ≡ * f x ];;

Check a8;;

End;;

Goal [ x : ? ];;					    # here we could deduce the type, too

# Make head reduction work;;
# This one is the same as the one above, with objects reversed;;

Goal [ _
      : @[ev][f,x,T,.@U]
      ≡ @[ev][@[λ;y][T,@[ev;_][f,y,T,@U]],x,T,.@U]
      : @U
      ];;

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
