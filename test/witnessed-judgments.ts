Mode TTS;;

Variable T Type;;
Variable x : T;;
Variable f : T -> @U;;

Check Judgment [ T -> @U Type ];;

Check Judgment { |- B Type } [ B -> @U Type ];;

Check Judgment LF (B:texp) ⟶ witnessed_istype B ⟶ witnessed_istype (@Pi B (_ ⟼ _ ⟼ @U));;

Check Judgment LF (B:texp) ⟶ witnessed_istype (@Pi B (_ ⟼ _ ⟼ @U));; # this succeeds because it's valid as an LF type, and there are no holes

Check Judgment [ _ : f : T -> @U ];;

Check Judgment [ x$ : f : T -> @U ];;				    # this succeeds also, counterintuitively -- it's a type without an object

Check Judgment [ _ : x : T ];;

Check Judgment [ _ : @ev[f,x,T,.@U] : @U ];;

Check Judgment [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U]: @U];;

Check Judgment [ @El[@ev[f,x,T,.@U],@wev[f$,x$]] Type ];;

Check Judgment [ @El[@ev[f,x,T,.@U],_] Type ];;

Check Judgment [ *@ev[f,x,T,.@U] Type ];;		    # * is notation for El

Check Judgment [ *@ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] Type ];;

Check Judgment [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[@λ[T,z.@ev[f,z,T,.@U]],x,T,.@U] : @U ];;

Check Judgment [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[f,x,T,.@U] : @U ];;

Check Judgment [ _ : @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ @ev[f,x,T,.@U] : @U ];;

Check Judgment [ _ : * @ev[@λ[T,y.@ev[f,y,T,.@U]],x,T,.@U] ≡ * @ev[f,x,T,.@U] ];;

Check Judgment [ _ : * @λ[T,y.f y] x ≡ * f x ];;

Check Judgment [ _ : * (λ y:T,f y) x ≡ * f x ];;

Check Judgment [ _ : * ((y:T) |-> f y) x ≡ * f x ] ;;

Check Judgment [ _ : * ((y:T) ⟼ f y) x ≡ * f x ] ;;

End;;

Check Judgment [ _ : x : _ ];;					    # here we could deduce the type, too

Lemma a8 : * (λ y:T,f y) x ≡ * f x;;

# Make head reduction work;;
# This one is the same as the one above, with objects reversed;;

Check Judgment [ _
      : @[ev;_][f,x,T,@U]
      ≡ @[ev;_][@[λ;y][T,@[ev;_][f,y,T,@U]],x,T,@U]
      : @U
      ];;

#   Local Variables:
#   compile-command: "make -C .. witnessed-judgments "
#   End:
