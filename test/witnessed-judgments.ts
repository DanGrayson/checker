Mode TTS;;

Variable T Type;;
Variable x : T;;
Variable f : T -> @U;;

Verify [ T -> @U Type ];;

Verify [ _ : f : T -> @U ];;

Verify [ _ : x : T ];;

Verify [ _ : @ev[f,x,T,.@U] : @U ];;

Verify [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U]: @U];;

Lemma a1 [ _ : f : T->@U ];;

Verify [ @El[@ev[f,x,T,.@U],@wev[f$,x$]] Type ];;

Verify [ @El[@ev[a1,x,T,.@U],@wev[a1$,x$]] Type ];;

# Verify [ @El[@ev[f,x,T,.@U],@wev[a1$,x$]] Type ];;

Verify [ @El[@ev[f,x,T,.@U],_] Type ];;

Verify [ *@ev[f,x,T,.@U] Type ];;		    # * is notation for El

Verify [ *@ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] Type ];;

Verify [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[@λ[T,z.@ev[f,z,T,.@U]],x,T,.@U] : @U ];;

Verify [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[f,x,T,.@U] : @U ];;

Verify [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[f,x,T,.@U] : @U ];;

Verify [ _ : * @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ * @ev[f,x,T,.@U] ];;

Verify [ _ : * @λ[T,y.f y] x ≡ * f x ];;

Verify [ _ : * (λ y:T,f y) x ≡ * f x ];;

Verify [ _ : * ((y:T) |-> f y) x ≡ * f x ] ;;

Verify [ _ : * ((y:T) ⟼ f y) x ≡ * f x ] ;;

End;;

Verify [ _ : x : _ ];;					    # here we could deduce the type, too

Lemma a8 : * (λ y:T,f y) x ≡ * f x;;

# Make head reduction work;;
# This one is the same as the one above, with objects reversed;;

Verify [ _
      : @[ev;_][f,x,T,@U]
      ≡ @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@U]],x,T,@U]
      : @U
      ];;

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
