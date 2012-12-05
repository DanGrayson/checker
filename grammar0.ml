(** Parsing: auxiliary functions. *)

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

let tDefinition (name:string) ((ulevel_context,tvars,ts_context):(uContext * (var list) * ((var * ts_expr) list))) (t:ts_expr) (d1:lf_expr option)
    : (var * position * lf_expr * lf_type) list 
    = 
  let pos = get_pos t in

  let UContext (uvars,ueqns) = ulevel_context in
  let ovars = List.map fst ts_context in
  let hts_context = List.map (fun (z,u) -> (z,u,newfresh (Var "h"))) ts_context in
  let hastvars = List.map (fun (z,u,hast) -> hast) hts_context in
  let allvars = List.flatten [uvars;tvars;ovars;hastvars] in

  let v0 = VarDefined(name,0) in
  let v1 = VarDefined(name,1) in

  let tm0 = Phi t in
  let tp0 = texp in
  let tm1 = match d1 with
  | Some tm1 -> tm1
  | None -> Phi(pos, new_hole()) in

  let tp1 = istype (Phi (nowhere 7 (APPLY(V v0, List.map var_to_lf allvars)))) in

  let g v t = LAMBDA(v,t) in
  let h sort v t = nowhere 8 (F_Pi(v,sort,t)) in
  let hast (z,u,h) t = nowhere 9 (F_Pi(h,hastype (var_to_lf z) (Phi u), t)) in

  let tm0 = List.fold_right g hastvars tm0 in
  let tm1 = List.fold_right g hastvars tm1 in
  let tp0 = List.fold_right hast hts_context tp0 in
  let tp1 = List.fold_right hast hts_context tp1 in

  let tm0 = List.fold_right g ovars tm0 in
  let tm1 = List.fold_right g ovars tm1 in
  let tp0 = List.fold_right (h oexp) ovars tp0 in
  let tp1 = List.fold_right (h oexp) ovars tp1 in

  let tm0 = List.fold_right g tvars tm0 in
  let tm1 = List.fold_right g tvars tm1 in
  let tp0 = List.fold_right (h texp) tvars tp0 in
  let tp1 = List.fold_right (h texp) tvars tp1 in

  let tm0 = List.fold_right g uvars tm0 in
  let tm1 = List.fold_right g uvars tm1 in
  let tp0 = List.fold_right (h uexp) uvars tp0 in
  let tp1 = List.fold_right (h uexp) uvars tp1 in

  [ 
    ( v0, pos, tm0, tp0 );
    ( v1, pos, tm1, tp1)
  ]

let oDefinition (name:string) ((ulevel_context,tc,ts_context):(uContext * (var list) * ((var * ts_expr) list))) (o:ts_expr) (t:ts_expr)
    : (var * position * lf_expr * lf_type) list 
    = 
  let pos = get_pos o in

  (* still have to wrap the lambdas around it : *)
  [
   ( VarDefined(name, 0), get_pos o, Phi o, oexp);
   ( VarDefined(name, 1), get_pos t, Phi t, texp);
   ( VarDefined(name, 2), get_pos o, Phi (pos, new_hole()), hastype (Phi o) (Phi t))
 ]

let teqDefinition _ _ _ _ = raise (Unimplemented "teqDefinition")

let oeqDefinition _ _ _ _ _ = raise (Unimplemented "oeqDefinition")
