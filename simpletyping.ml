  (* 
     Here we implement the function "tau" from the paper.  It produces the type of an o-expression o in a context g,
     even if the expression is not yet known to be well-formed.
   *)

open Basic
open Typesystem

let rec tau g = function
  | Ovariable v -> (try (List.assoc v g) with Not_found -> raise (Basic.Error ("unbound variable, not in context: " ^ (Printer.ovartostring v))))
  | O_u x -> T_U (Uplus(x,1))
  | O_j (m1,m2) -> Pi(T_U m1,(OVarDummy,T_U m2))
  | O_ev (o1,o2,(x,t)) -> Substitute.tsubst [(x,o2)] t
  | O_lambda (t,(x,o)) -> Pi(t, (x, tau ((x,t) :: g) o))
  | O_forall (m1,m2,_,(_,_)) -> T_U (Umax( m1, m2))
  | O_pair _
  | O_pr1 _
  | O_pr2 _
  | O_total _
  | O_pt -> T_U (Unumeral 0)
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
  | O_rr1 _
      -> raise NotImplemented