# -*- coding: utf-8 -*-

Define A (u : Ulevel; u=u) (t : [U](u)) := [El](t); (El_type u t h$1).

Define B (u : Ulevel) (t : [U](u)) := [El](t); (El_type $a $a $a).

Variable u1 : Ulevel.

Check LF ([B.0] ([next] u1) ([u] u1) (u_univ u1)).

Check LF ([B.1] ([next] u1) ([u] u1) (u_univ u1)).

Show 7.

#   Local Variables:
#   compile-command: "make demo "
#   End:
