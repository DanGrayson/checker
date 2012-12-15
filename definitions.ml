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

let wrap vartypes (def,pos,tm,tp) = (def, pos, fold lamb vartypes tm, fold pi vartypes tp)

let term_or_hole pos = function
  | Some tm -> tm
  | None -> hole pos

let ist_2 pos v = [pos, v,texp; pos, newfresh (Var "i"), ist pos v]

let ist_s pos v = sigma (pos,v,texp) (ist pos v)

let ist_1 pos v = [pos, v, ist_s pos v]

let hast_2 pos v t = [pos, v, oexp; pos, newfresh (Var "h"), hast pos v t]

let hast_s pos v t = sigma (pos,v,oexp) (hast pos v t)

let hast_1 pos v t = [pos, v,hast_s pos v t]

let ist_12 = if disable_sigma then ist_2 else ist_1

let hast_12 = if disable_sigma then hast_2 else hast_1

let augment uvars ueqns tvars o_vartypes = List.flatten (
    List.flatten [
    List.map (fun (pos,x)    -> [pos,x,uexp]) uvars;
    List.map (fun (pos,(l,r)) -> [pos, newfresh (Var "u"), ulevel_equality l r]) ueqns;
    List.map (fun (pos,x) -> ist_12 pos x) tvars;
    List.map (fun ((pos,x),t) -> hast_12 pos x t) o_vartypes
  ])

let tDefinition name (UContext (uvars,ueqns),tvars,o_vartypes) t d1 = 
  let pos = get_pos t in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let name1 = VarDefined(name,1) in
  let j = term_or_hole pos d1 in
  let r = List.map (wrap vartypes) 
    (
     if disable_sigma 
     then
       [ (name0, pos, t, texp); (name1, pos, j, istype (apply pos name0 vartypes)) ]
     else 
       let tj = pos, CONS(t,j) in 
       let v = newfresh (Var "T") in
       [ ( name0, pos, tj, ist_s pos v ) ]
    ) in
  r

let oDefinition name (UContext(uvars,ueqns),tvars,o_vartypes) o (t:lf_expr) d1 =
  let pos = get_pos o in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let name1 = VarDefined(name,1) in
  let j = term_or_hole pos d1 in
  let r = List.map (wrap vartypes) 
    (
     if disable_sigma
     then
       [ (name0, pos, o, oexp); (name1, pos, j, hastype (apply pos name0 vartypes) t) ]
     else
       let oj = pos, CONS(o, j ) in
       let v = newfresh (Var "o") in
       [ ( name0, pos, oj , hast_s pos v t ) ]
    ) in
  r

let teqDefinition _ _ _ _ = raise (Unimplemented "teqDefinition")

let oeqDefinition _ _ _ _ _ = raise (Unimplemented "oeqDefinition")

open Printf
open Printer

let addDefinition env v pos o t = def_bind v pos o t env

let defCommand env defs = 
  List.fold_left
    (fun env (v, pos, tm, tp) -> 
      printf "Define %a = %a\n" _v v  _e tm;
      flush stdout;
      printf "       %a : %a\n" _v v  _t tp; flush stdout;
      let tp' = Lfcheck.type_validity env tp in
      printf "       %a : %a [after tactics]\n" _v v  _t tp'; flush stdout;
      let tm' = Lfcheck.type_check env tm tp in
      printf "       %a = %a [after tactics]\n" _v v  _e tm'; flush stdout;
      let tm'' = Lfcheck.term_normalization env tm' tp' in
      printf "       %a = %a [normalized]\n" _v v  _e tm''; flush stdout;
      let tp'' = Lfcheck.type_normalization env tp' in
      printf "       %a : %a [normalized]\n" _v v  _t tp''; flush stdout;
      addDefinition env v pos tm' tp'
    ) 
    env defs

let tDefCommand env (name,parms,t,d1) = 
  let defs = tDefinition name (fixParmList parms) t d1 in
  defCommand env defs

let oDefCommand env (name,parms,o,t,d1) = 
  let defs = oDefinition name (fixParmList parms) o t d1 in
  defCommand env defs

let teqDefCommand env (name,parms,t1,t2) = 
  let defs = teqDefinition name (fixParmList parms) t1 t2 in
  defCommand env defs

let oeqDefCommand env (name,parms,o1,o2,t) = 
  let defs = oeqDefinition name (fixParmList parms) o1 o2 t in
  defCommand env defs

(* 
  Local Variables:
  compile-command: "make definitions.cmo "
  End:
 *)
