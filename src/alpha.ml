open Error
open Variables
open Typesystem
open Helpers

module type S =
  sig
    val uequiv     : uContext -> lf_expr -> lf_expr -> bool
    val term_equiv : uContext -> lf_expr -> lf_expr -> bool
    val type_equiv : uContext -> lf_type -> lf_type -> bool
  end

module Make(Ueq: Universe.Equivalence) : S = struct

  let uequiv = Ueq.term_equiv

  let rec term_equiv uc x x' =
      match (unmark x, unmark x') with
      | LAMBDA (_,body), LAMBDA (_,body') -> 
	  term_equiv uc body body'
      | APPLY(h,args), APPLY(h',args') -> (
	  match (h,h') with
	  | U _, U _ -> uequiv uc x x'
	  | _ -> 
	      h = h' && 
	      args_compare (term_equiv uc) args args')
      | CONS(x,y), CONS(x',y') -> 
	  term_equiv uc x x' && 
	  term_equiv uc y y'
      | _ -> false

  let rec type_equiv uc x x' =
      match (unmark x, unmark x') with
      | F_Singleton (x,t) , F_Singleton (x',t') -> 
	  term_equiv uc x x' && 
	  type_equiv uc t t'
      | F_Pi(_,t,u), F_Pi(_,t',u') -> 
	  type_equiv uc t t' && 
	  type_equiv uc u u'
      | F_Sigma(_,t,u), F_Sigma(_,t',u') -> 
	  type_equiv uc t t' && 
	  type_equiv uc u u'
      | F_Apply(h,args), F_Apply(h',args') -> 
	  h = h' && 
	  List.for_all2 (term_equiv uc) args args'
      | _ -> false

end

module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)

(*
  Local Variables:
  compile-command: "make -C .. src/alpha.cmo "
  End:
 *)
