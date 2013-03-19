# All the base judgments, and what would satisfy them as evidence.
# The binders are present in order to produce well-formed types.
# ( Here "with" means a satisfactory term would be a pair. )

Check TS : (T:texp) =>             [ T Type ];;          # a proof that T is a type

Check TS : (T:texp) =>             |- T Type;;           # T with a proof that T is a type

Check TS :                         Type;;                # a t-expression with a proof that it is a type

Check TS : (T:texp) => (t:oexp) => [ t : T ];;           # a proof that t has type T

Check TS : (T:texp) => (t:oexp) => |- t : T;;            # t with a proof that t has type T

Check TS : (T:texp) =>             : T;;                 # an o-expression with a proof that it has type T

Check TS : (T:texp) => (U:texp) => [ T ≡ U ];;           # a proof that T ≡ U (type equality)

Check TS : (T:texp) => (t:oexp)
                    => (u:oexp) => [ t ≡ u : T ];;       # a proof that t ≡ u : T (object equality)

# Here are the base judgments again, but this time with binders for pairs;;  For example,
# { |- T Type } denotes a parameter T whose value is a t-expression with a proof that it is a type;;

Check TS : { |- T Type }        [ T Type ];;             # T with a proof that T is a type

Check TS : { |- T Type }        |- T Type;;              # T with a proof that T is a type

Check TS :                      Type;;                   # a t-expression with a proof that it is a type

Check TS : { |- T Type, t:T }   [ t : T ];;              # a proof that t has type T

Check TS : { |- T Type, t:T }   |- t : T;;               # t with a proof that t has type T

Check TS : { |- T Type }        : T;;                    # an o-expression with a proof that it has type T

Check TS : { |- T U Type }      [ T ≡ U ];;              # a proof that T ≡ U (type equality)

Check TS : { |- T Type, t u:T } [ t ≡ u : T ];;          # a proof that t ≡ u : T (object equality)

# Here are the judgments involving ulevel equality:

Check TS : (T:texp) => (t:oexp) =>
      		       (u:oexp) => [ t ~ u : T ];;       # ulevel equivalence for o-expressions
Check TS : (T:texp) => (U:texp) => [ T ~ U Type ];;      # ulevel equivalence for t-expressions
Check TS : (u:uexp) => (v:uexp) => [ u ~ v Ulevel ];;    # ulevel equivalence for u-expressions

#   Local Variables:
#   compile-command: "make -C ;;;; judgments "
#   End:
