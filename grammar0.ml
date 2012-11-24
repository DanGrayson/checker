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

let tDefinition name : ((uContext * tContext * oContext) * expr) -> string * definition = 
  function ((uc,tc,oc),body) -> 
    (name,[
     (0,body,texpr_TF);
     (1,nowhere EmptyHole,istype_TF body)
   ])
let oDefinition _ = raise (Error.Unimplemented "oDefinition")
let teqDefinition _ = raise (Error.Unimplemented "teqDefinition")
let oeqDefinition _ = raise (Error.Unimplemented "oeqDefinition")
