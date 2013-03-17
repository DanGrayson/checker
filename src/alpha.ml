(* should rename this file *)

(* We still have to implement the relation called ~ in the paper, which ignores inessential subterms. *)

open Error
open Variables
open Typesystem
open Helpers

module type S =
  sig
    val uequiv     : uContext -> expr -> expr -> bool
    val term_equiv : uContext -> int -> expr -> expr -> bool
    val type_equiv : uContext -> int -> lf_type -> lf_type -> bool
  end

module Make(Ueq: Universe.Equivalence) : S = struct

  let uequiv = Ueq.term_equiv

  let rec term_equiv uc shift x x' =
      match (unmark x, unmark x') with
      | TEMPLATE (_,body), TEMPLATE (_,body') -> 
	  term_equiv uc shift body body'
      | BASIC(h,args), BASIC(h',args') -> (
	  match (h,h') with
	  | U _, U _ -> uequiv uc x x'
	  | V (VarRel i), V (VarRel j) -> shift + i = j
	  | _ -> 
	      h = h' && 
	      args_compare (term_equiv uc shift) args args')
      | PAIR(x,y), PAIR(x',y') -> 
	  term_equiv uc shift x x' && 
	  term_equiv uc shift y y'
      | _ -> false

  let rec type_equiv uc shift x x' =
      match (unmark x, unmark x') with
      | F_Singleton (x,t) , F_Singleton (x',t') -> 
	  term_equiv uc shift x x' && 
	  type_equiv uc shift t t'
      | F_Pi(_,t,u), F_Pi(_,t',u') -> 
	  type_equiv uc shift t t' && 
	  type_equiv uc shift u u'
      | F_Sigma(_,t,u), F_Sigma(_,t',u') -> 
	  type_equiv uc shift t t' && 
	  type_equiv uc shift u u'
      | F_Apply(h,args), F_Apply(h',args') -> 
	  h = h' && 
	  List.for_all2 (term_equiv uc shift) args args'
      | _ -> false

end

module UEqual = Make(Universe.Equal)
module UEquivA = Make(Universe.EquivA)

(*
  Local Variables:
  compile-command: "make -C .. src/alpha.cmo "
  End:
 *)
