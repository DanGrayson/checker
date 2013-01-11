(** parsing aids for [grammar.mly] *)

open Printf
open Printer
open Typesystem
open Error
open Variables
open Names

let lookup_label pos name =
  try List.assoc name Names.lf_expr_head_strings 
  with Not_found as e -> fprintf stderr "%a: unknown expression label: [%s]\n%!" _pos pos name; raise e

let lookup_type_constant pos name =
  try List.assoc name Names.string_to_type_constant
  with Not_found as e -> Printf.fprintf stderr "%a: unknown type constant %s\n%!" _pos pos name; raise e

type binder_judgment = ULEV | IST | HAST of lf_expr

let add_single v t u = F_Pi(v, t, u)

let app (hd,reversed_args) arg = (hd, ARG(arg,reversed_args))

let car (hd,reversed_args) = (hd, CAR reversed_args)

let cdr (hd,reversed_args) = (hd, CDR reversed_args)

type binder = position * var * lf_type

let subst_binder sub (b:binder) = 
  match b with
  | (pos,v,a) -> (pos,v,Substitute.subst_type sub a)

let subst_binder_list sub (b:binder list) = List.map (subst_binder sub) b

let subst_binder_option sub (b:binder option) =
  match b with
  | Some b -> Some (subst_binder sub b)
  | None -> None

let bind_sigma binder b =
  match binder with
  | (pos,v,a) -> 
      let v' = newfresh v in
      let v'' = var_to_lf_pos pos v' in
      let b = Substitute.subst_type (v,v'') b in
      let v = v' in
      with_pos pos (F_Sigma(v,a,b))

let bind_pi binder b =
  match binder with 
  | (pos,v,a) -> 
      let v' = newfresh v in
      let v'' = var_to_lf_pos pos v' in
      let b = Substitute.subst_type (v,v'') b in
      let v = v' in
      with_pos pos (F_Pi(v,a,b))

let bind_arrow (pos,a) b = with_pos pos (F_Pi(newunused(),a,b))

let bind_some_sigma binder b =
  match binder with
  | Some binder -> bind_sigma binder b
  | None -> b

let rec bind_pi_list_rev binders b =
  match binders with
  | [] -> b
  | binder :: binders -> bind_pi_list_rev binders (bind_pi binder b)

let apply_vars f binders =
  Substitute.apply_args f (List.fold_right (fun (pos,v,a) accu -> (ARG(var_to_lf_pos pos v,accu))) binders END)

 (** for a type p of the form (e:E) ** J we return (e,E),J *)
let unbind_pair p : binder option * lf_type =
  match unmark p with
  | F_Sigma(v,a,b) -> Some (get_pos p,v,a), b
  | _ -> None, p

let good_var_name p v =
  match unbind_pair p with
  | Some (pos,v,a), b -> v
  | None, b -> v

let is_t_o_expr t = 
  match unmark t with
  | F_Apply(( F_texp | F_oexp ), _) -> true
  | _ -> false  

 (** Suppose t has the form (e:E) ** J and u has the form (f:F) ** K.  We think
     of an instance of t as providing a parametrized expression of type E
     together with a judgment of type J about the expression, and similarly for
     u.  We return a new type describing a parametrized expression of type E->F
     together with a judgment about it, of type (E**J)->K.  The resulting type
     looks like (f: (e:E)->F) ** (e : (e':E)**J)->K. *)
let pi1_pairs_implication (vpos,v) t u =
  let (e,j) = unbind_pair t in
  let (f,k) = unbind_pair u in
  match e,f with
  | Some (epos,e,ee), Some(fpos,f,ff) ->
      let bt = 
	match unmark ff with
	| F_Singleton s -> let (_,bt) = Lfcheck.strip_singleton s in bt
	| _ -> ff in
      let k = 
	if is_t_o_expr bt 
	then bind_sigma (fpos,f,with_pos fpos (F_Singleton(var_to_lf_pos fpos f,bt))) k
	else k in
      let v_1 = with_pos epos (APPLY(V v, CAR END)) in
      let k = Substitute.subst_type (v,v_1) k in
      let k = Substitute.subst_type (f,with_pos fpos (APPLY(V f, ARG (v_1, END)))) k in
      let t = bind_sigma (epos,e,ee) j in
      let k = bind_pi (epos,v,t) k in
      let ff = bind_pi (epos,v,ee) ff in
      let r = bind_sigma (fpos,f,ff) k in
      r
  | Some (epos,e,ee), None ->
      let v_1 = with_pos epos (APPLY(V v, CAR END)) in
      let k = Substitute.subst_type (v,v_1) k in
      let t = bind_sigma (epos,e,ee) j in
      let k = bind_pi (epos,v,t) k in
      k
  | _ -> 
      printf " pi1_pairs_implication case unimplemented\n%!";
      raise NotImplemented

 (** for a type p of the form (p_1:P_1) -> ... -> (p_n:P_n) -> (e:E) ** J we
     return [p_n,P_n;...;p_1,P_n],(e,E),J. *)
let unbind_relative p : binder list * binder option * lf_type =
  let rec repeat binders p =
    match unmark p with
    | F_Pi(v,a,b) -> repeat ((get_pos p,v,a) :: binders) b
    | F_Sigma(v,a,b) -> binders, Some (get_pos p,v,a), b
    | _ -> [], None, bind_pi_list_rev binders p
  in
  repeat [] p

 (** Suppose t has the form P -> (e:E) ** J and u has the form Q -> (f:F) ** K.
     We think of an instance of t as providing a parametrized expression of
     type P -> E together with a judgment of type J about the expression, and
     similarly for u.  We return a new type describing a parametrized
     expression of type (P->E)->(Q->F) together with a judgment about it, of
     type (P->J)->K.  The resulting type looks like (e:P -> E) -> Q -> (f:F) **
     (P -> J) -> K.  All this goes through if t has the form P_1 -> ... -> P_n
     -> (e:E) ** J, and similarly for u, because we can rewrite t in terms of
     P = P_1 ** ... ** P_n. *)
let pi1_relative_implication (vpos,v) t u =
  let (p,e,j) = unbind_relative t in
  let (q,f,k) = unbind_relative u in
  match e with
  | Some (pos,e,ee) ->
      let j = Substitute.subst_type (e,apply_vars (var_to_lf_pos pos v) (List.rev p)) j in
      let ee = bind_pi_list_rev p ee in
      let j = bind_pi_list_rev p j in
      let k = arrow j k in
      let j = bind_pi_list_rev q (bind_some_sigma f k) in
      let t = bind_pi (pos,v,ee) j in
      t
  | None -> raise NotImplemented

let simple_implication (vpos,v) t u =
  printf " simple_implication\n\t v = %a\n\t t = %a\n\t u = %a\n%!" _v v _t t _t u;
  let (e,j) = unbind_pair t in
  printf "\t j = %a\n%!" _t j;
  let r = match e with
  | Some(wpos,w,a) -> 
      printf "\t w = %a\n\t a = %a\n%!" _v w _t a;
      let u = bind_arrow (wpos,j) u in
      bind_pi (vpos,v,a) u
  | None -> bind_pi (vpos,v,j) u in
  printf "\t r = %a\n%!" _t r;
  r

let pi1_implication (v,t) u = (
  match !Toplevel.binder_mode with
  | Toplevel.Binder_mode_simple -> simple_implication
  | Toplevel.Binder_mode_relative -> pi1_relative_implication
  | Toplevel.Binder_mode_pairs -> pi1_pairs_implication
 ) v t u

let apply_binder pos (c:(var marked * lf_expr) list) (v : var marked) (t1 : lf_type) (t2 : lf_expr -> lf_type) (u : lf_type) = 
  (* syntax is { v_1 : T_1 , ... , v_n : T_n |- v Type } u  or  { v_1 : T_1 , ... , v_n : T_n |- v:T } u *)
  (* t1 is texp or oexp; t2 is (fun t -> istype t) or (fun o -> hastype o t) *)
  let (vpos,v) = v in
  let c = List.map (fun ((vpos,v),t) -> (vpos,v), (vpos, F_Sigma(v,oexp,hastype (var_to_lf_pos pos v) t))) c in
  let t = pos, F_Sigma(v,t1,t2 (var_to_lf_pos pos v)) in
  let t = List.fold_right pi1_implication c t in
  let u = pi1_implication ((vpos,v),t) u in
  unmark u
 
(* 
  Local Variables:
  compile-command: "make -C .. src/parse.cmo "
  End:
 *)
