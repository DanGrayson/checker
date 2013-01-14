# -*- coding: utf-8 -*-
# abbreviations for TS expressions 

Definition LF UU : (M:uexp) ⟶ texp := @[U].

Definition LF uu : (M:uexp) ⟶ oexp := @[u].

Definition LF next : (M:uexp) ⟶ uexp := @[next].

Definition LF Empty : texp := @[Empty].

Definition LF Pt : texp := @[Pt].

Definition LF pt : oexp := @[pt].

Definition LF tt : oexp := @[tt].

#   Local Variables:
#   compile-command: "make -C .. abbreviations "
#   End:
