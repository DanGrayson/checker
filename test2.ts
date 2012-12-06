Variable u v : Ulevel ; u < v .
Axiom TS a : [Pt]().
Axiom LF T : texp.
Axiom LF i : (istype T).
Check Universes.

Define compose (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f x)) : T->V.

Show 100.

#   Local Variables:
#   compile-command: "make run2 "
#   End:
