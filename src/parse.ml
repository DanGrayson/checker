(** parsing aids for [grammar.mly] *)

open Printf
open Printer
open Typesystem
open Error
open Variables
open Names
open Helpers

let lookup_label pos name =
  try list_assoc2 name (lf_expr_head_table())
  with Not_found as e -> fprintf stderr "%a: unknown expression label: @[%s]\n%!" _pos pos name; raise e

let lookup_type_constant pos name =
  try list_assoc2 name lf_type_constant_table
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

type binder = position * identifier * lf_type

let show_binders bname b ename e = 
  iteri (fun i (pos,v,t) -> printf " %s.%d = %a:%a\n%!" bname i _i v _t (empty_environment,t)) b;
  match e with 
  | Some (pos,v,t) -> printf " %s = %a:%a\n%!" ename _i v _t (empty_environment,t)
  | None -> ()

let bind_sigma binder b =
  match binder with
  | (pos,v,a) -> pos, make_F_Sigma a (v,b)

let bind_pi binder b =
  match binder with
  | (pos,v,a) -> pos, make_F_Pi a (v,b)

let bind_pi_reassemble binder b =
  match binder with
  | (pos,v,a) -> pos, make_F_Pi_reassemble a (v,b)

let bind_some_sigma binder b =
  match binder with
  | Some binder -> bind_sigma binder b
  | None -> b

let rec bind_pi_list_rev binders b =
  match binders with
  | [] -> b
  | binder :: binders -> bind_pi_list_rev binders (bind_pi_reassemble binder b)

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
  try
    let rec repeat binders p =
      match unmark p with
      | F_Pi(v,a,b) -> repeat ((get_pos p,v,a) :: binders) b
      | F_Sigma(v,a,b) -> binders, Some (get_pos p,v,a), b
      | _ -> raise Not_found
    in
    repeat [] p
  with Not_found -> [], None, p

 (** Here "**" is our notation for Sigma type.
     
     Suppose 

        t = P_(m-1) -> ... -> P_0 -> (e:E) ** J

     and

        u = Q_(n-1) -> ... Q_0 -> (f:F) ** K

     We think of an instance of t as providing a parametrized expression of
     type P_(m-1) -> ... -> P_0 -> E together with a judgment of type J about
     the expression, and similarly for u.  We return a new type describing a
     parametrized expression of type 

        (P_(m-1) -> ... -> P_0 -> E) -> Q_(n-1) -> ... Q_0 -> F

     together with a judgment about it, of type 

        (P_(m-1) -> ... -> P_0 -> J) -> K

     The resulting type looks like 

        (e':P_(m-1) -> ... -> P_0 -> E) -> Q_(n-1) -> ... Q_0 -> (f:F) ** (P_(m-1) -> ... -> P_0 -> J) -> K.

     J gets rewritten by replacing each e (relative index 0) by 
     (e' p_(m-1) ... p_0) and decrementing the relative indices of its other
     exposed variables.

     K gets rewritten by incrementing the relative indices of its exposed variables.
  *)

let pi1_debug = false

let pi1_implication ((vpos,v),t) u =
  if pi1_debug then printf "\npi1_implication:\n t = %a\n%!" _t (empty_environment,t);
  if pi1_debug then printf " u = %a\n%!" _t (empty_environment,u);
  let (p,e,j) = unbind_relative t in
  let m = List.length p in
  if pi1_debug then show_binders "p" p "e" e;
  if pi1_debug then printf " j = %a\n%!" _t (empty_environment,j);
  let (q,f,k) = unbind_relative u in
  let n = List.length q + match f with Some _ -> 1 | None -> 0 in
  if pi1_debug then show_binders "q" q "f" f;
  if pi1_debug then printf " k = %a\n%!" _t (empty_environment,k);
  match e with
  | Some (pos,e,ee) ->
      let j = Substitute.subst_type (with_pos pos (apply_vars (VarRel (m+n)) (List.rev p))) j in
      if pi1_debug then printf " j = substituted = %a\n%!" _t (empty_environment,j);
      let ee = bind_pi_list_rev p ee in
      if pi1_debug then printf " ee = bind_pi_list_rev p ee = %a\n%!" _t (empty_environment,ee);
      let j = bind_pi_list_rev p j in
      if pi1_debug then printf " j = bind_pi_list_rev p j = %a\n%!" _t (empty_environment,j);
      let k = rel_shift_type 1 k in
      if pi1_debug then printf " k = rel_shift_type 1 k = %a\n%!" _t (empty_environment,k);
      let k = arrow j k in
      if pi1_debug then printf " k = arrow j k = %a\n%!" _t (empty_environment,k);
      let j = bind_pi_list_rev q (bind_some_sigma f k) in
      if pi1_debug then printf " j = bind_pi_list_rev q (bind_some_sigma f k) = %a\n%!" _t (empty_environment,j);
      let r = bind_pi (pos,v,ee) j in
      if pi1_debug then printf " r = bind_pi (pos,v,ee) j = %a\n%!" _t (empty_environment,r);
      r
  | None -> raise NotImplemented

let apply_binder pos (c:(identifier marked * lf_expr) list) (v : identifier marked) (t1 : lf_type) (t2 : position -> identifier -> lf_type) (u : lf_type) =
  (* syntax is { v_1 : T_1 , ... , v_n : T_n |- v Type } u  or  { v_1 : T_1 , ... , v_n : T_n |- v:T } u *)
  (* t1 is texp or oexp; t2 is (fun t -> istype t) or (fun o -> hastype o t) *)
  let (vpos,v) = v in
  let c = List.map (fun ((vpos,v),t) -> (vpos,v), (vpos, make_F_Sigma oexp (v,hastype (var_to_lf_pos pos (Var v)) t))) c in
  let t = pos, make_F_Sigma t1 (v,t2 pos v) in
  let t = List.fold_right pi1_implication c t in
  let u = pi1_implication ((vpos,v),t) u in
  unmark u

let apply_judgment_binder pos (j:lf_type) (u:lf_type) =
  (* just like pi1_implication above, except t consists just of j, with no p or e *)
  if pi1_debug then printf "\napply_judgment_binder:\n j = %a\n u = %a\n%!" _t (empty_environment,j) _t (empty_environment,u);
  let (q,f,k) = unbind_relative u in
  if pi1_debug then show_binders "q" q "f" f;
  if pi1_debug then printf " k = %a\n%!" _t (empty_environment,k);
  let n = List.length q + match f with Some _ -> 1 | None -> 0 in
  let j = Substitute.subst_type (var_to_lf_pos pos (VarRel n)) j in
  if pi1_debug then printf " j = substituted = %a\n%!" _t (empty_environment,j);
  let k = rel_shift_type 1 k in
  if pi1_debug then printf " k = rel_shift_type 1 k = %a\n%!" _t (empty_environment,k);
  let k = arrow j k in
  if pi1_debug then printf " k = arrow j k = %a\n%!" _t (empty_environment,k);
  let r = bind_pi_list_rev q (bind_some_sigma f k) in
  if pi1_debug then printf " r = bind_pi_list_rev q (bind_some_sigma f k) = %a\n%!" _t (empty_environment,r);
  r

(*
  Local Variables:
  compile-command: "make -C .. src/parse.cmo "
  End:
 *)

