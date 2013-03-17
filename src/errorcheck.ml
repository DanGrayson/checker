(** error messages for type checking *)

open Error
open Names
open Printer

exception TermEquivalenceFailure
exception TypeEquivalenceFailure
exception SubtypeFailure

let err env pos msg = raise (TypeCheckingFailure (env, [], [pos, msg]))

let errmissingarg env pos a = err env pos ("missing next argument, of type "^lf_type_to_string env a)

let mismatch_type env pos t pos' t' =
  raise (TypeCheckingFailure (env, [], [
         pos , "expected type " ^ lf_type_to_string env t;
         pos', "to match      " ^ lf_type_to_string env t']))

let mismatch_term_type env e t =
  raise (TypeCheckingFailure (env, [], [
               get_pos e, "error: expected term\n\t" ^ expr_to_string env e;
               get_pos t, "to be compatible with type\n\t" ^ lf_type_to_string env t]))

let mismatch_term_type_type env e s t =
  raise (TypeCheckingFailure (env, [], [
               get_pos e, "error: expected term\n\t" ^ expr_to_string env e;
               get_pos s, "of type\n\t" ^ lf_type_to_string env s;
               get_pos t, "to be compatible with type\n\t" ^ lf_type_to_string env t]))

let mismatch_term_t env pos x pos' x' t =
  raise (TypeCheckingFailure (env, [], [
                    pos , "error: expected term\n\t" ^ expr_to_string env x ;
                    pos',      "to match\n\t" ^ expr_to_string env x';
               get_pos t,       "of type\n\t" ^ lf_type_to_string env t]))

let mismatch_term env pos x pos' x' =
  raise (TypeCheckingFailure (env, [], [
                    pos , "error: expected term\n\t" ^ expr_to_string env x;
                    pos',      "to match\n\t" ^ expr_to_string env x']))

let function_expected env f t =
  raise (TypeCheckingFailure (env, [], [
                    get_pos f, "error: encountered a non-function\n\t" ^ expr_to_string env f;
                    get_pos t, "of type\n\t" ^ lf_type_to_string env t]))

let ts_function_expected env f t =
  raise (TypeCheckingFailure (env, [], [
                    get_pos f, "error: encountered a non-function\n\t" ^ expr_to_string env f;
                    get_pos t, "of type\n\t" ^ expr_to_string env t]))

let mismatch_term_tstype_tstype env e s t =
  raise (TypeCheckingFailure (env, [], [
               get_pos e, "error: expected term\n\t" ^ ts_expr_to_string env e;
               get_pos s, "of type\n\t" ^ ts_expr_to_string env s;
               get_pos t, "to be compatible with type\n\t" ^ ts_expr_to_string env t]))
