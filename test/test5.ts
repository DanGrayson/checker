# pi1-relative binding

Check LF : pi Type.

Check LF : T Type |- U Type |- t::T |- pi Type.

Check LF : (T:texp) -> ( x::T |- U Type ).

Check LF : (T:texp) -> ( x::T |- pi Type ).

Check LF : T Type |- ( x::T |- U Type) |- pi Type.

Check LF : T Type |- ( x::T |- y::T |- U Type) |- pi Type.

#   Local Variables:
#   compile-command: "make -C .. test5 "
#   End:
