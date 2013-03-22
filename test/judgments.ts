# All the base judgments, and what would satisfy them as evidence.
# The binders are present in order to produce well-formed types.
# ( Here "with" means a satisfactory term would be a pair. )

Verify  (T:texp) =>             [ T Type ];;          # a proof that T is a type

Verify  (T:texp) =>             |- T Type;;           # T with a proof that T is a type

Verify                          Type;;                # a t-expression with a proof that it is a type

Verify  (T:texp) => (t:oexp) => [ t : T ];;           # a proof that t has type T

Verify  (T:texp) => (t:oexp) => |- t : T;;            # t with a proof that t has type T

Verify  (T:texp) =>             : T;;                 # an o-expression with a proof that it has type T

Verify  (T:texp) => (U:texp) => [ T ≡ U ];;           # a proof that T ≡ U (type equality)

Verify  (T:texp) => (t:oexp)
                    => (u:oexp) => [ t ≡ u : T ];;       # a proof that t ≡ u : T (object equality)

# Here are the base judgments again, but this time with binders for pairs;;  For example,
# { |- T Type } denotes a parameter T whose value is a t-expression with a proof that it is a type;;

Verify  { |- T Type }        [ T Type ];;             # T with a proof that T is a type

Verify  { |- T Type }        |- T Type;;              # T with a proof that T is a type

Verify                       Type;;                   # a t-expression with a proof that it is a type

Verify  { |- T Type, t:T }   [ t : T ];;              # a proof that t has type T

Verify  { |- T Type, t:T }   |- t : T;;               # t with a proof that t has type T

Verify  { |- T Type }        : T;;                    # an o-expression with a proof that it has type T

Verify  { |- T U Type }      [ T ≡ U ];;              # a proof that T ≡ U (type equality)

Verify  { |- T Type, t u:T } [ t ≡ u : T ];;          # a proof that t ≡ u : T (object equality)

# Here are the judgments involving ulevel equality:

Verify  (T:texp) => (t:oexp) =>
      		       (u:oexp) => [ t ~ u : T ];;       # ulevel equivalence for o-expressions
Verify  (T:texp) => (U:texp) => [ T ~ U Type ];;      # ulevel equivalence for t-expressions
Verify  (u:uexp) => (v:uexp) => [ u ~ v Ulevel ];;    # ulevel equivalence for u-expressions

#   Local Variables:
#   compile-command: "make -C .. judgments "
#   End:
