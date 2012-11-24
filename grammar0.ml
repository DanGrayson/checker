(** Parsing: auxiliary functions. *)

open Typesystem
open Helpers

type parm =
  | UParm of uContext
  | TParm of tContext
  | OParm of oContext

let fixParmList (p:parm list) : uContext * tContext * oContext = (* this code has to be moved somewhere to use the context *)
  let rec fix us ts os p =
    match p with 
    | UParm u :: p -> 
	if List.length ts > 0 or List.length os > 0 then raise (Error.GeneralError "expected universe-level variables first");
	fix (u::us) ts os p
    | TParm t :: p -> 
	if List.length os > 0 then raise (Error.Unimplemented "a type parameter after an object parameter");
	fix us (t::ts) os p
    | OParm o :: p -> fix us ts (o::os) p
    | [] -> ( 
	let tc = List.flatten (List.rev_append ts [])
	and oc = List.flatten (List.rev_append os [])
	and uc = match (List.rev_append us []) with
	| [] -> emptyUContext
	| (uc :: []) -> uc
	| _ -> raise (Error.Unimplemented "merging of universe level variable lists")
	in (uc,tc,oc))
  in fix [] [] [] p

let tDefinition (name:string) ((uc,tc,oc):(uContext * tContext * oContext)) (t:expr) : string * definition = 
    (name,[
     (0,t,texpr_TF);
     (1,new_hole (),istype_TF t)
   ])
let oDefinition (name:string) ((uc,tc,oc):(uContext * tContext * oContext)) (o:expr) (t:expr) : string * definition = 
    (name,[
     (0,o,oexpr_TF);
     (1,t,texpr_TF);
     (2,new_hole (),hastype_TF o t)
   ])
let teqDefinition _ = raise (Error.Unimplemented "teqDefinition")
let oeqDefinition _ = raise (Error.Unimplemented "oeqDefinition")
