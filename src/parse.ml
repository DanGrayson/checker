(** parsing aids for [grammar.mly] *)

open Printf
open Printer
open Typesystem
open Error
open Variables
open Names
open Helpers

let lookup_label pos name =
  try List.assoc name Names.lf_expr_head_strings
  with Not_found as e -> fprintf stderr "%a: unknown expression label: @[%s]\n%!" _pos pos name; raise e

let lookup_type_constant pos name =
  try List.assoc name Names.string_to_type_constant
  with Not_found -> F_undeclared_type_constant(pos,name)

type binder_judgment =
  | ULEV
  | IST
  | HAST of lf_expr
  | W_HAST of lf_expr * lf_expr
  | W_TEQ of lf_expr * lf_expr
  | W_OEQ of lf_expr * lf_expr * lf_expr

let app (hd,reversed_args) arg = (hd, ARG(arg,reversed_args))

let car (hd,reversed_args) = (hd, CAR reversed_args)

let cdr (hd,reversed_args) = (hd, CDR reversed_args)

type binder = position * var * lf_type

let bind_sigma binder b =
  match binder with
  | (pos,v,a) -> pos, make_F_Sigma a (v,b)

let bind_pi binder b =
  match binder with
  | (pos,v,a) -> pos, make_F_Pi a (v,b)

let bind_some_sigma binder b =
  match binder with
  | Some binder -> bind_sigma binder b
  | None -> b

let rec bind_pi_list_rev binders b =
  match binders with
  | [] -> b
  | binder :: binders -> bind_pi_list_rev binders (bind_pi binder b)

let apply_vars f binders =
  let i = ref 0 in
  APPLY(V f, 
	List.fold_right 
	  (fun (pos,v,a) args -> 
	    let r = ARG(var_to_lf_pos pos (VarRel !i),args) in
	    incr i;
	    r) 
	  binders
	  END)

 (** for a type p of the form (e:E) ** J we return (e,E),J *)
let unbind_pair p : binder option * lf_type =
  match unmark p with
  | F_Sigma(v,a,b) -> Some (get_pos p,v,a), b
  | _ -> None, p

let good_var_name p v =
  match unbind_pair p with
  | Some (pos,v,a), b -> v
  | None, b -> v

 (** for a type p of the form (p_1:P_1) -> ... -> (p_n:P_n) -> (e:E) ** J we
     return [p_n,P_n;...;p_1,P_n],Some (e,E),J.  If there is no Sigma-type
     inseid, then return [],None,p
  *)
let unbind_relative p : binder list * binder option * lf_type =
  let rec repeat binders p =
    match unmark p with
    | F_Pi(v,a,b) -> repeat ((get_pos p,v,a) :: binders) b
    | F_Sigma(v,a,b) -> binders, Some (get_pos p,v,a), b
    | _ -> [], None, bind_pi_list_rev binders p (* it would be better to raise an exception here, instead of reassembling p *)
  in
  repeat [] p

 (** Suppose t has the form P -> (e:E) ** J and u has the form Q -> (f:F) ** K.
     We think of an instance of t as providing a parametrized expression of
     type P -> E together with a judgment of type J about the expression, and
     similarly for u.  We return a new type describing a parametrized
     expression of type (P->E)->(Q->F) together with a judgment about it, of
     type (P->J)->K.  The resulting type looks like (e:P -> E) -> Q -> (f:F) **
     (P -> J) -> K.  All this goes through if t has the form P_(n-1) -> ... -> P_0
     -> (e:E) ** J, and similarly for u, because we can rewrite t in terms of
     P = P_1 ** ... ** P_n. *)
let pi1_implication ((vpos,v),t) u =
  printf "pi1_implication:\n t = %a\n%!" _t t;
  printf " u = %a\n%!" _t u;
  let (p,e,j) = unbind_relative t in
  let m = List.length p in
  printf " j = %a\n%!" _t j;
  let (q,f,k) = unbind_relative u in
  let n = List.length q in
  printf " k = %a\n%!" _t k;
  match e with
  | Some (pos,e,ee) ->
      let j = Substitute.subst_type (with_pos pos (apply_vars (VarRel (m+1+n)) (List.rev p))) j in
      printf " j = %a\n%!" _t j;
      let ee = bind_pi_list_rev p ee in
      printf " ee = %a\n%!" _t ee;
      let j = bind_pi_list_rev p j in
      printf " j = %a\n%!" _t j;
      let j = rel_shift_type (-1) j in
      printf " j = %a\n%!" _t j;
      let k = rel_shift_type 1 k in
      printf " k = %a\n%!" _t k;
      let k = arrow j k in
      printf " k = %a\n%!" _t k;
      let j = bind_pi_list_rev q (bind_some_sigma f k) in
      printf " j = %a\n%!" _t j;
      let t = bind_pi (pos,v,ee) j in
      printf " t = %a\n%!" _t t;
      t
  | None -> raise NotImplemented

let apply_binder pos (c:(var marked * lf_expr) list) (v : var marked) (t1 : lf_type) (t2 : position -> var -> lf_type) (u : lf_type) =
  (* syntax is { v_1 : T_1 , ... , v_n : T_n |- v Type } u  or  { v_1 : T_1 , ... , v_n : T_n |- v:T } u *)
  (* t1 is texp or oexp; t2 is (fun t -> istype t) or (fun o -> hastype o t) *)
  let (vpos,v) = v in
  let c = List.map (fun ((vpos,v),t) -> (vpos,v), (vpos, make_F_Sigma oexp (v,hastype (var_to_lf_pos pos v) t))) c in
  let t = pos, make_F_Sigma t1 (v,t2 pos v) in
  let t = List.fold_right pi1_implication c t in
  let u = pi1_implication ((vpos,v),t) u in
  unmark u

let apply_judgment_binder pos (j:lf_type) (u:lf_type) =
  (* just like pi1_implication above, except t consists just of j, with no p or e *)
  let (q,f,k) = unbind_relative u in
  let k = arrow j k in
  bind_pi_list_rev q (bind_some_sigma f k)

(*
  Local Variables:
  compile-command: "make -C .. src/parse.cmo "
  End:
 *)

