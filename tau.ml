  (* 
     Here we implement the function "tau" from the paper.  It produces the type of an o-expression o in a context g,
     even if the expression is not yet known to be well-formed.
   *)

open Typesystem

let rec tau (g:(oVar*tExpr) list) ((o,pos):oExpr) = nowhere (
  match o with
  | OEmptyHole -> raise (TypingError(pos, "empty hole, type undetermined, internal error"))
  | ONumberedEmptyHole _ -> raise (TypingError(pos, "empty hole, type undetermined, internal error"))
  | Onumeral _ -> T_nat
  | Ovariable v -> (
      try strip_pos(List.assoc v g) 
      with
	Not_found -> 
	  raise (TypingError(pos, "unbound variable, not in context: " ^ (Printer.ovartostring v)))
     )
  | O_u x -> T_U (nowhere(Uplus(x,1)))
  | O_j (m1,m2) -> Pi(nowhere(T_U m1),(OVarUnused,nowhere(T_U m2)))
  | O_ev (o1,o2,(x,t)) -> strip_pos(Substitute.tsubst [(x,o2)] t)
  | O_lambda (t,(x,o)) -> Pi(t, (x, tau ((x,t) :: g) o))
  | O_forall (m1,m2,_,(_,_)) -> T_U (nowhere(Umax(m1, m2)))
  | O_pair _
  | O_pr1 _
  | O_pr2 _
  | O_total _
  | O_pt -> T_U uuu0
  | O_pt_r _ -> raise NotImplemented
  | O_tt
  | O_coprod _
  | O_ii1 _
  | O_ii2 _
  | Sum _
  | O_empty
  | O_empty_r _
  | O_c _
  | O_ic_r _
  | O_ic _
  | O_paths _
  | O_refl _
  | O_J _
  | O_rr0 _
  | O_rr1 _ -> raise NotImplemented
  | O_def (d,u,t,c) -> raise NotImplemented
 )
