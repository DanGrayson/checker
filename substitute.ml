(** Substitution. *) 

open Error
open Variables
open Typesystem
open Helpers
open Names
open Printer
open Printf

let fresh v subl =
  let v' = newfresh v in
  v', (v,var_to_lf v') :: subl

let show_subs (subl : (var * lf_expr) list) =
  printf " subs =\n";
  List.iter (fun (v,e) -> printf "   %a => %a\n" p_var v p_expr e) subl

let spy_counter = ref 0

let spy p subber subl e = 
  if !debug_mode then (
    let n = !spy_counter in
    incr spy_counter;
    show_subs subl;
    printf " in  %d = %a\n" n p e; flush stdout;
    let e = subber subl e in
    printf " out %d = %a\n" n p e; flush stdout;
    e)
  else subber subl e

let rec subst_list (subl : (var * lf_expr) list) es = List.map (subst subl) es

and subst_spine subl = function
  | ARG(x,a) -> ARG(subst subl x, subst_spine subl a)
  | FST a -> FST(subst_spine subl a)
  | SND a -> SND(subst_spine subl a)
  | NIL -> NIL

and subst subl e = spy p_expr subst'' subl e

and subst'' subl = function
  | CAN (pos,e) as d -> (
      match e with
      | APPLY(V v,args) -> (
          try 
            let z = List.assoc v subl in
            match args with
            | NIL -> z
            | args -> (
		let args = subst_spine subl args in 
                match z with 
                | CAN(zpos,APPLY(f,brgs)) -> CAN(pos,APPLY(f, join_args brgs args))
                | LAMBDA _ as f -> apply_args pos f args
                | _ ->
                    printf "about to replace %a by %a in %a, not implemented\n"
                      p_var v
                      p_expr z
                      p_expr d; flush stdout;
                    raise (Unimplemented_expr d))
          with Not_found -> d)
      | APPLY(label,args) -> CAN(pos, APPLY(label,subst_spine subl args))
     )
  | PAIR(pos,x,y) -> PAIR(pos,subst subl x,subst subl y)
  | LAMBDA(v, body) -> 
      let (v,body) = subst_fresh subl (v,body) in
      LAMBDA(v, body)

and subst_fresh subl (v,e) =
  let (v,subl) = fresh v subl in
  v, subst subl e  

and apply_args pos (f:lf_expr) args =
  let rec repeat f args = 
    match f with
    | CAN(pos,APPLY(f,brgs)) -> CAN(pos,APPLY(f, join_args brgs args))
    | LAMBDA(v,body) -> (
        match args with
        | ARG(x,args) -> repeat (subst [(v,x)] body) args
        | FST args -> repeat (pi1 body) args
        | SND args -> repeat (pi2 body) args
        | NIL -> raise (GeneralError "too few arguments"))
    | x -> (
        match args with
        | NIL -> x
        | _ -> raise (GeneralError "too few arguments"))
  in repeat f args

let rec subst_type_list (subl : (var * lf_expr) list) ts = List.map (subst_type subl) ts

and subst_type subl t = spy p_type subst_type'' subl t

and subst_type'' (subl : (var * lf_expr) list) (pos,t) = 
  (pos,
   match t with
   | F_Pi(v,a,b) ->
       let a = subst_type subl a in
       let (v,b) = subst_type_fresh subl (v,b) in
       F_Pi(v,a,b)
   | F_Sigma(v,a,b) -> 
       let a = subst_type subl a in
       let (v,b) = subst_type_fresh subl (v,b) in
       F_Sigma(v,a,b)
   | F_APPLY(label,args) -> F_APPLY(label, subst_list subl args)
   | F_Singleton(e,t) -> F_Singleton( subst subl e, subst_type subl t ))

and subst_type_fresh subl (v,t) =
  let (v,subl) = fresh v subl in
  let t = subst_type subl t in
  v,t

let rec subst_kind_list (subl : (var * lf_expr) list) ts = List.map (subst_kind subl) ts

and subst_kind subl k = spy p_kind subst_kind'' subl k

and subst_kind'' (subl : (var * lf_expr) list) k = 
   match k with
   | K_type -> K_type
   | K_Pi(v,a,b) -> 
       let a = subst_type subl a in
       let (v,b) = subst_kind_fresh subl (v,b) in K_Pi(v, a, b)

and subst_kind_fresh subl (v,t) =
  let (v,subl) = fresh v subl in
  v, subst_kind subl t  

let preface subber (v,x) e = subber [(v,x)] e

let subst = preface subst

let subst_type = preface subst_type

let subst_kind = preface subst_kind

(* 
  Local Variables:
  compile-command: "make substitute.cmo "
  End:
 *)
