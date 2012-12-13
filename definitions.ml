open Error
open Variables
open Typesystem
open Names
open Helpers

let emptyUContext = UContext ([],[])
let mergeUContext : uContext -> uContext -> uContext =
  function UContext(uvars,eqns) -> function UContext(uvars',eqns') -> UContext(List.rev_append uvars' uvars,List.rev_append eqns' eqns)

type parm =
  | UParm of uContext
  | TParm of var list
  | OParm of (var * lf_expr) list

let fixParmList (p:parm list) : uContext * (var list) * ((var * lf_expr) list) =
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

let apply f vartypes = (nowhere 7 (APPLY(V f, list_to_spine(List.map (var_to_lf @@ fst) vartypes))))

let ist x = istype (var_to_lf x)

let hast x t = hastype (var_to_lf x) t

let lamb (v,t1) t2 = nowhere 99 (LAMBDA(v,t2))

let pi   (v,t1) t2 = nowhere 8 (F_Pi(v,t1,t2))

let fold = List.fold_right

let wrap vartypes (def,pos,tm,tp) = (def, pos, fold lamb vartypes tm, fold pi vartypes tp)

let term_or_hole pos = function
  | Some tm -> tm
  | None -> hole pos

let sigma v t u = nowhere 43 (F_Sigma(v,t,u))

let ist_2 v = [v,texp; newfresh (Var "i"), ist  v]

let ist_s v = sigma v texp (ist v)

let ist_1 v = [v,ist_s v]

let hast_2 v t = [v,oexp; newfresh (Var "h"), hast v t]

let hast_s v t = sigma v oexp (hast v t)

let hast_1 v t = [v,hast_s v t]

let augment uvars ueqns tvars o_vartypes = List.flatten (
    List.flatten [
    List.map (fun  x    -> [x,uexp]) uvars;
    List.map (fun (l,r) -> [newfresh (Var "u"), ulevel_equality l r]) ueqns;
    List.map (fun  x    -> ist_2 x) tvars;
    List.map (fun (x,t) -> hast_2 x t) o_vartypes
  ])

let tDefinition name (UContext (uvars,ueqns),tvars,o_vartypes) t d1 = 
  let pos = get_pos t in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let name1 = VarDefined(name,1) in
  let j = term_or_hole pos d1 in
  List.map (wrap vartypes) 
    (
     if disable_sigma 
     then
       [ (name0, pos, t, texp); (name1, pos, j, istype (apply name0 vartypes)) ]
     else 
       let tj = pos,CONS(t,j) in 
       let v = newfresh (Var "T") in
       [ ( name0, pos, tj, ist_s v ) ]
    )

let oDefinition name (UContext(uvars,ueqns),tvars,o_vartypes) o (t:lf_expr) d1 =
  let pos = get_pos o in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let name0 = Var name in
  let name1 = VarDefined(name,1) in
  let j = term_or_hole pos d1 in
  List.map (wrap vartypes) 
    (
     if disable_sigma
     then
       [ (name0, pos, o, oexp); (name1, pos, j, hastype (apply name0 vartypes) t) ]
     else
       let oj = pos, CONS(o, j ) in
       let v = newfresh (Var "o") in
       [ ( name0, pos, oj , hast_s v t ) ]
    )

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
