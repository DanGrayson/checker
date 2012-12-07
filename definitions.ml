open Error
open Typesystem
open Names
open Helpers

let emptyUContext = UContext ([],[])
let mergeUContext : uContext -> uContext -> uContext =
  function UContext(uvars,eqns) -> function UContext(uvars',eqns') -> UContext(List.rev_append uvars' uvars,List.rev_append eqns' eqns)

type parm =
  | UParm of uContext
  | TParm of var list
  | OParm of (var * ts_expr) list

let fixParmList (p:parm list) : uContext * (var list) * ((var * ts_expr) list) =
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

let apply f vartypes = Phi (nowhere 7 (APPLY(V f, List.map (var_to_lf @@ fst) vartypes)))

let ist x = istype (var_to_lf x)

let hast x t = hastype (var_to_lf x) (Phi t)

let lamb (v,t1) t2 = LAMBDA(v,t2)

let pi   (v,t1) t2 = nowhere 8 (F_Pi(v,t1,t2))

let augment uvars ueqns tvars o_vartypes = List.flatten (
    List.flatten [
    List.map (fun  x    -> [x,uexp]) uvars;
    List.map (fun (l,r) -> [newfresh (Var "u"), ulevel_equality (Phi l) (Phi r)]) ueqns;
    List.map (fun  x    -> [x,texp; newfresh (Var "i"), ist  x  ]) tvars;
    List.map (fun (x,t) -> [x,oexp; newfresh (Var "h"), hast x t]) o_vartypes
  ])

let fold = List.fold_right

let wrap vartypes (def,pos,tm,tp) = (def, pos, fold lamb vartypes tm, fold pi vartypes tp)

let hole pos = Phi(pos, new_hole())

let term_or_hole pos = function
  | Some tm -> tm
  | None -> hole pos

let tDefinition name (UContext (uvars,ueqns),tvars,o_vartypes) t d1 = 
  let pos = get_pos t in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let v = newfresh (Var name) in
  List.map (wrap vartypes) 
    [ 
      ( Var name, pos, PAIR(pos, Phi t, term_or_hole pos d1), nowhere 43 (F_Sigma(v,texp,istype (var_to_lf v))) )
      ]

let oDefinition name (UContext(uvars,ueqns),tvars,o_vartypes) o t d1 =
  let pos = get_pos o in
  let vartypes = augment uvars ueqns tvars o_vartypes in
  let def_0 = VarDefined(name,0) in
  List.map (wrap vartypes)
    [
     ( def_0             , get_pos o, Phi o              , oexp );
     ( VarDefined(name,1), get_pos t, term_or_hole pos d1, hastype (apply def_0 vartypes) (Phi t)) ]

let teqDefinition _ _ _ _ = raise (Unimplemented "teqDefinition")

let oeqDefinition _ _ _ _ _ = raise (Unimplemented "oeqDefinition")

open Printf
open Printer

let addDefinition env v pos o t = def_bind v pos o t env

let defCommand env defs = 
  List.fold_left
    (fun env (v, pos, tm, tp) -> 
      printf "Define %a = %a\n" p_var v  p_expr tm;
      flush stdout;
      let tp' = Lfcheck.type_validity env tp in
      let tm' = Lfcheck.type_check pos env tm tp in
      let tm'' = Lfcheck.term_normalization env tm' tp' in
      let tp'' = Lfcheck.type_normalization env tp' in
      printf "       %a = %a [after tactics]\n" p_var v  p_expr tm';
      printf "       %a = %a [normalized]\n" p_var v  p_expr tm'';
      printf "       %a : %a\n" p_var v  p_type tp;
      printf "       %a : %a [after tactics]\n" p_var v  p_type tp';
      printf "       %a : %a [normalized]\n" p_var v  p_type tp'';
      flush stdout;
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
