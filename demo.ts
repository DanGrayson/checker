# -*- coding: utf-8 -*-

# Check LF El_type.

Define A (u : Ulevel) (t : [U](u)) := *t; (El_type u t h$1).

Define A (u : Ulevel) (t : [U](u)) := *t; (El_type $a $a $a).

Define A (u : Ulevel) (t : [U](u)) := *t; (El_type $2 $2 $2).

Variable u1 : Ulevel.

Check LF ([A.0] ([next] u1) ([u] u1) (u_univ u1)).

# Check LF ([A.1] ([next] u1) ([u] u1) (u_univ u1)).

# Show.

#   Local Variables:
#   compile-command: "make demo "
#   End:
