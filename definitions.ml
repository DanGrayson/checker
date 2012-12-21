open Printer
open Printf
open Error
open Variables
open Typesystem
open Names
open Helpers
open Substitute

let emptyUContext = UContext ([],[])
let mergeUContext : uContext -> uContext -> uContext =
  function UContext(uvars,eqns) -> function UContext(uvars',eqns') -> UContext(List.rev_append uvars' uvars,List.rev_append eqns' eqns)

type parm =
  | UParm of uContext
  | TParm of var marked list
  | OParm of (var marked * lf_expr) list

let fixParmList (p:parm list) : uContext * (var marked list) * ((var marked * lf_expr) list) =
  let rec fix us ts os p =
    match p with 
    | UParm u :: p -> 
	if List.length ts > 0 or List.length os > 0 then raise (GeneralError "expected universe-level variables first");
	fix (u::us) ts os p
    | TParm t :: p -> 
	if List.length os > 0 then raise (Unimplemented "a type parameter after an object parameter");
	fix us (t::ts) os p
    | OParm o :: p -> fix us ts (o::os) p
    | [] -> ( 
	let tc = List.flatten (List.rev_append ts [])
	and ts_context = List.flatten (List.rev_append os [])
	and ulevel_context = match (List.rev_append us []) with
	| [] -> emptyUContext
	| (ulevel_context :: []) -> ulevel_context
	| _ -> raise (Unimplemented "merging of universe level variable lists")
	in (ulevel_context,tc,ts_context))
  in fix [] [] [] p

let ( @@ ) f g x = f (g x)

let apply pos f vartypes = with_pos pos (APPLY(V f, list_to_spine(List.map (fun (pos,v,t) -> var_to_lf_pos pos v) vartypes)))

let ist pos x = istype (var_to_lf_pos pos x)

let hast pos x t = hastype (var_to_lf_pos pos x) t

let lamb (pos,v,t) o = 
  let (v,o) = subst_fresh pos (v,o) in
  with_pos (get_pos o) (LAMBDA(v,o))

let pi (pos,v,t) u = 
  let (v,u) = subst_type_fresh pos (v,u) in
  with_pos pos (F_Pi(v,t,u))

let sigma (pos,v,t) u = 
  let (v,u) = subst_type_fresh pos (v,u) in
  with_pos pos (F_Sigma(v,t,u))

let fold = List.fold_right

let wrap vartypes (def,pos,tm,tp) = (def, pos, with_pos pos (unmark (fold lamb vartypes tm)), with_pos pos (unmark (fold pi vartypes tp)))

let _vartypes file vartypes = List.iter (fun (_,v,t) -> fprintf file "  %a : %a\n" _v v _t t) vartypes

let term_or_default_tactic pos = function
  | Some tm -> tm
  | None -> pos, APPLY(TAC (Tactic_name "default"), END)

let ist_2 pos v = [pos, v,texp; pos, newfresh (Var "i"), ist pos v]

let ist_s pos v = sigma (pos,v,texp) (ist pos v)

let ist_1 pos v = [pos, v, ist_s pos v]

let hast_2 pos v t = [pos, v, oexp; pos, newfresh (Var "h"), hast pos v t]

let hast_s pos v t = sigma (pos,v,oexp) (hast pos v t)

let hast_1 pos v t = [pos, v,hast_s pos v t]

let augment uvars ueqns tvars o_vartypes = List.flatten (
  List.flatten [
  List.map (fun (pos,x)    -> [pos,x,uexp]) uvars;
  List.map (fun (pos,(l,r)) -> [pos, newfresh (Var "u"), ulevel_equality l r]) ueqns;
  List.map (fun (pos,x) -> ist_1 pos x) tvars;
  List.map (fun ((pos,x),t) -> hast_1 pos x t) o_vartypes ])

let is_uexp t =
  match unmark t with
  | F_APPLY(F_uexp _,_) -> true
  | _ -> false

let make_subs vartypes = 
  List.flatten (
    List.map 
      (fun (pos,v,t) -> 
	if is_uexp t then []
	else [(v, pi1 (var_to_lf_pos pos v))]) 
      vartypes)

let map_subs subs vartypes = if subs = [] then vartypes else List.map (fun (pos,v,t) -> pos,v,subst_type_l subs t) vartypes

let tDefinition dpos name (UContext (uvars,ueqns),tvars,o_vartypes) t d1 = 
  let pos = get_pos t in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let j = term_or_default_tactic pos d1 in
  let subs = make_subs vartypes in
  let vartypes = map_subs subs vartypes in
  let t = subst_l subs t in
  let tj = pos, CONS(t,j) in 
  let v = newfresh (Var "T") in
  List.map (wrap vartypes) [ ( name0, pos, tj, ist_s pos v ) ]

let theorem dpos name (UContext(uvars,ueqns),tvars,o_vartypes) (t:lf_expr) d1 =
  let pos = get_pos t in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let oj = term_or_default_tactic pos d1 in	(* a single hold for the pair: proof term and derivation *)
  let subs = make_subs vartypes in
  let vartypes = map_subs subs vartypes in
  let t = subst_l subs t in
  let v = newfresh (Var "o") in
  List.map (wrap vartypes) [ ( name0, pos, oj , hast_s pos v t ) ]

let oDefinition dpos name (UContext(uvars,ueqns),tvars,o_vartypes) o (t:lf_expr) d1 =
  let pos = get_pos o in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let j = term_or_default_tactic dpos d1 in
  let subs = make_subs vartypes in
  let vartypes = map_subs subs vartypes in
  let o = subst_l subs o in
  let t = subst_l subs t in
  let oj = dpos, CONS(o, j ) in
  let v = newfresh (Var "o") in
  List.map (wrap vartypes) [ ( name0, dpos, oj , hast_s pos v t ) ]

let teqDefinition dpos _ _ _ _ = raise (Unimplemented "teqDefinition")

let oeqDefinition dpos _ _ _ _ _ = raise (Unimplemented "oeqDefinition")

open Printf
open Printer

let addDefinition env v pos o t = def_bind v pos o t env

let defCommand env defs = 
  List.fold_left
    (fun env (v, pos, tm, tp) -> 
      printf "Define %a = %a\n" _v v  _e tm;
      flush stdout;
      printf "       %a : %a\n%!" _v v  _t tp;
      let tp' = Lfcheck.type_validity env tp in
      if not (Alpha.UEqual.type_equiv empty_uContext tp tp') then
      printf "       %a : %a [after tactics]\n%!" _v v  _t tp';
      let tm' = Lfcheck.type_check env tm tp in
      if not (Alpha.UEqual.term_equiv empty_uContext tm tm') then
      printf "       %a = %a [after tactics]\n%!" _v v  _e tm';
      let tm'' = Lfcheck.term_normalization env tm' tp' in
      if not (Alpha.UEqual.term_equiv empty_uContext tm' tm'') then
      printf "       %a = %a [normalized]\n%!" _v v  _e tm'';
      printf "       %a = %a [normalized, TS format]\n%!" _v v  _ts tm'';
      let tp'' = Lfcheck.type_normalization env tp' in
      if not (Alpha.UEqual.type_equiv empty_uContext tp' tp'') then
      printf "       %a : %a [normalized]\n%!" _v v  _t tp'';
      addDefinition env v pos tm' tp'
    ) 
    env defs

let tDefCommand env (pos,name,parms,t,d1) = 
  let defs = tDefinition pos name (fixParmList parms) t d1 in
  defCommand env defs

let theoremCommand env (pos,name,deriv,thm) = 
  defCommand env [ Var name, pos, deriv, thm ]

let oDefCommand env (pos,name,parms,o,t,d1) = 
  let defs = oDefinition pos name (fixParmList parms) o t d1 in
  defCommand env defs

let teqDefCommand env (pos,name,parms,t1,t2) = 
  let defs = teqDefinition pos name (fixParmList parms) t1 t2 in
  defCommand env defs

let oeqDefCommand env (pos,name,parms,o1,o2,t) = 
  let defs = oeqDefinition pos name (fixParmList parms) o1 o2 t in
  defCommand env defs

(* 
  Local Variables:
  compile-command: "make definitions.cmo "
  End:
 *)
