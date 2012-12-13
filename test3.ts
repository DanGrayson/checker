
Define compose1 (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f x)) : T->V.

Define compose2 (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := g(f t) : V.

Define compose3 (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f _)) : T->V.

End.

# in coq it looks like this:

# Definition compose1 (T U V:Type) (g:U -> V) (f:T -> U) (t:T) : V.
# Proof.
#  apply g. apply f. assumption.
# Qed.




#   Local Variables:
#   compile-command: "make run3 "
#   End:
