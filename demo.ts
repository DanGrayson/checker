# -*- coding: utf-8 -*-

Define A (u : Ulevel) (t : [U](u)) := *t; (El_type u t h$1).

Define B (u : Ulevel) (t : [U](u)) := *t; (El_type $a $a $a).

Define C (u : Ulevel) (t : [U](u)) := *t; (El_type $2 $2 $2).

Variable u1 : Ulevel.

Check LF ([C.0] ([next] u1) ([u] u1) (u_univ u1)).

Check LF ([C.1] ([next] u1) ([u] u1) (u_univ u1)).

Show 7.

#   Local Variables:
#   compile-command: "make demo "
#   End:
