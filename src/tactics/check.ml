open Helpers
open Typesystem
open Lfcheck
open Printer
open Printf

(** print the arguments and their types *)
let check surr env pos t args =
  args_iter 
    (fun x -> 
      let (x',t) = type_synthesis env x in
      let t = un_singleton t in
      let x' = term_normalization env x' t in
      printf "$check = %a\n       = %a [normalized]\n       : %a\n%!" _e (env,x) _e (env,x') _t (env,t);
    )
    (fun () -> ())
    (fun () -> ())
    args;
  TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/check.cmo "
  End:
 *)
