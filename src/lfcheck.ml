(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    [EEST]: Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676-722.
*)

(*

  We probably don't handle types such as [Pi x:A, Singleton(B)] well.

  We should implement hash consing so the alpha equivalence testing doesn't slow things down too much.

*)

open Error
open Variables
open Typesystem
open Names
open Printer
open Substitute
open Printf
open Helpers
open Tau
open Printer

exception TermEquivalenceFailure
exception TypeEquivalenceFailure
exception SubtypeFailure

let abstraction1 pos (env:context) = function
  | ARG(t,ARG((_,LAMBDA(x, _)),_)) -> ts_bind pos (x,t) env
  | _ -> env

let abstraction2 pos (env:context) = function
  | ARG(_,ARG(_,ARG(n,ARG((_,LAMBDA(x,_)),_)))) -> ts_bind pos (x,(get_pos n, make_T_El n)) env
  | _ -> env

let abstraction3 pos (env:context) = function
  | ARG(f,ARG(_,ARG((_,LAMBDA(x, _)),_))) -> (
      try
	let tf = tau env f in (
	match unmark tf with
	| APPLY(T T_Pi, ARG(t, _)) -> ts_bind pos (x,t) env
	| _ -> env)
      with NotImplemented ->
	printf "%a: warning: abstraction3: \"tau\" not implemented for %a\n%!" _pos_of f _e f;
	env)
  | _ -> env

let ts_binders = [
  ((O O_lambda, 1), abstraction1);
  ((T T_Pi, 1), abstraction1);
  ((T T_Sigma, 1), abstraction1);
  ((O O_forall, 3), abstraction2);
  ((O O_ev, 2), abstraction3)
]

let apply_ts_binder env i e =
  let pos = get_pos e in
  match unmark e with
  | APPLY(h,args) -> (
      try
        (List.assoc (h,i) ts_binders) pos env args
      with
        Not_found -> env)
  | _ -> internal ()

let try_alpha = true

let err env pos msg = raise (TypeCheckingFailure (env, [pos, msg]))

let errmissingarg env pos a = err env pos ("missing next argument, of type "^lf_type_to_string a)

let mismatch_type env pos t pos' t' = 
  raise (TypeCheckingFailure (env, [
         pos , "expected type " ^ lf_type_to_string t;
         pos', "to match      " ^ lf_type_to_string t']))

let mismatch_term_type env e t =
  raise (TypeCheckingFailure (env, [
               get_pos e, "expected term\n\t" ^ lf_expr_to_string e;
               get_pos t, "to be compatible with type\n\t" ^ lf_type_to_string t]))

let mismatch_term_type_type env e s t =
  raise (TypeCheckingFailure (env, [
               get_pos e, "expected term\n\t" ^ lf_expr_to_string e;
               get_pos s, "of type\n\t" ^ lf_type_to_string s;
               get_pos t, "to be compatible with type\n\t" ^ lf_type_to_string t]))

let mismatch_term_t env pos x pos' x' t = 
  raise (TypeCheckingFailure (env, [
                    pos , "expected term\n\t" ^ lf_expr_to_string x ;
                    pos',      "to match\n\t" ^ lf_expr_to_string x';
               get_pos t,       "of type\n\t" ^ lf_type_to_string t]))

let mismatch_term env pos x pos' x' = 
  raise (TypeCheckingFailure (env, [
                    pos , "expected term\n\t" ^ lf_expr_to_string x;
                    pos',      "to match\n\t" ^ lf_expr_to_string x']))

let function_expected env f t =
  raise (TypeCheckingFailure (env, [
                    get_pos f, "encountered a non-function\n\t" ^ lf_expr_to_string f;
                    get_pos t, "of type\n\t" ^ lf_type_to_string t]))

let rec strip_singleton ((_,(_,t)) as u) = match t with
| F_Singleton a -> strip_singleton a
| _ -> u

(* background assumption: all types in the environment have been verified *)

let apply_tactic surr env pos t = function
  | Tactic_hole n -> TacticFailure
  | Tactic_name name ->
      let tactic = 
        try List.assoc name !tactics
        with Not_found -> err env pos ("unknown tactic: " ^ name) in
      tactic surr env pos t
  | Tactic_index n ->
      let (v,u) = 
        try List.nth env n 
        with Failure nth -> err env pos ("index out of range: "^string_of_int n) in
      TacticSuccess (var_to_lf_pos pos v)

let rec natural_type (env:context) (x:lf_expr) : lf_type =
  if true then internal ();          (* this function is unused, because "unfold" below does what we need for weak head reduction *)
  (* assume nothing *)
  (* see figure 9 page 696 [EEST] *)
  let pos = get_pos x in 
  match unmark x with
  | APPLY(l,args) -> 
      let t = head_to_type env pos l in
      let rec repeat i args t =
        match args, unmark t with
        | ARG(x,args), F_Pi(v,a,b) -> repeat (i+1) args (subst_type (v,x) b)
        | ARG _, _ -> err env pos "at least one argument too many"
        | CAR args, F_Sigma(v,a,b) -> repeat (i+1) args a
        | CAR _, _ -> err env pos "pi1 expected a pair (2)"
        | CDR args, F_Sigma(v,a,b) -> repeat (i+1) args b
        | CDR _, _ -> err env pos "pi2 expected a pair (2)"
        | END, F_Pi(v,a,b) -> errmissingarg env pos a
        | END, t -> t
      in nowhere 5 (repeat 0 args t)
  | LAMBDA _ -> err env pos "LF lambda expression found, has no natural type"
  | CONS _ -> err env pos "LF pair found, has no natural type"

let car_passed_term pos head args_passed = with_pos pos (APPLY(head,reverse_spine (CAR args_passed)))

let subst_car_passed_term v pos head args_passed b = subst_type (v, car_passed_term pos head args_passed) b

let rec head_reduction (env:context) (x:lf_expr) : lf_expr =
  (* see figure 9 page 696 [EEST] *)
  (* assume x is not a pair or a function *)
  (* raises Not_found if there is no head reduction *)
  (* we work out the natural type of each partial head path in the loop below,
     while looking for singletons, instead of calling the routine natural_type *)
  let pos = get_pos x in
  match unmark x with
  | APPLY(h,args) -> (
      match h with
      | TAC _ -> internal ()
      | (O _|T _) -> raise Not_found (* we know the constants in our signature don't involve singleton types *)
      | FUN(f,t) -> (
	  (* merge this case with the case below ??? *)
	  if true then raise NotImplemented;
	  (* if f reduces to a lambda expression, then we can apply it, so implement that case *)
          try
            let f = head_reduction env f in with_pos pos (APPLY(FUN(f,t),args))
          with Not_found ->
            apply_args f args)
      | head -> 
	  let t = head_to_type env pos head in
	  let args_passed = END in
	  let rec repeat t args_passed args =
	    match unmark t, args with
	    | F_Singleton s, args -> let (x,t) = strip_singleton s in apply_args x args
	    | F_Pi(v,a,b), ARG(x,args) -> repeat (subst_type (v,x) b) (ARG(x,args_passed)) args
	    | F_Sigma(v,a,b), CAR args -> repeat a (CAR args_passed) args
	    | F_Sigma(v,a,b), CDR args -> repeat (subst_car_passed_term v pos head args_passed b) (CDR args_passed) args
	    | _, END -> raise Not_found
	    | _ ->
		printf "%a: head_reduction case not covered: head %a of type %a applied to args %a\n%!" _pos pos _h head _t t _s args;
		print_context (Some 10) stdout env;
		internal () in
	  repeat t args_passed args
     )
  | CONS _ | LAMBDA _ -> internal ()	(* head reduction is not defined for pairs or functions *)

let rec head_normalization (env:context) (x:lf_expr) : lf_expr =
  (* see figure 9 page 696 [EEST] *)
  try head_normalization env (head_reduction env x)
  with Not_found -> x

(** Type checking and equivalence routines. *)

let rec term_equivalence (env:context) (x:lf_expr) (y:lf_expr) (t:lf_type) : unit =
  (* assume x and y have already been verified to be of type t *)
  (* see figure 11, page 711 [EEST] *)
  if !debug_mode then printf " term_equivalence\n\t x=%a\n\t y=%a\n\t t=%a\n%!" _e x _e y _t t;
  (if try_alpha && Alpha.UEqual.term_equiv empty_uContext x y then () else
  match unmark t with
  | F_Singleton _ -> ()
  | F_Sigma (v,a,b) -> 
      term_equivalence env (pi1 x) (pi1 y) a;
      term_equivalence env (pi2 x) (pi2 y) (subst_type (v,(pi1 x)) b)
  | F_Pi (v,a,b) ->
      let w = newfresh v in		(* in case x or y contains v as a free variable *)
      let w' = var_to_lf w in 
      let b = subst_type (v,w') b in
      let env = (w,a) :: env in
      let xres = apply_args x (ARG(w',END)) in
      let yres = apply_args y (ARG(w',END)) in
      term_equivalence env xres yres b
  | F_Apply(j,args) ->
      if j == F_uexp then (
	if !debug_mode then printf "warning: ulevel comparison judged true: %a = %a\n%!" _e x _e y;
       )
      else (
	let x = head_normalization env x in
	let y = head_normalization env y in
	if !debug_mode then printf "\t new x=%a\n\t new y=%a\n%!" _e x _e y;
	let t' = path_equivalence env x y in
	if !debug_mode then printf "\t new t'=%a\n\n%!" _t t';
	subtype env t' t			(* this was not spelled out in the paper, which concerned base types only *)
	  ));
  if !debug_mode then printf " term_equivalence okay\n%!"

and path_equivalence (env:context) (x:lf_expr) (y:lf_expr) : lf_type =
  (* assume x and y are head reduced *)
  (* see figure 11, page 711 [EEST] *)
  if !debug_mode then printf " path_equivalence\n\t x=%a\n\t y=%a\n%!" _e x _e y;
  let t = 
  (
  match x,y with
  | (xpos,APPLY(head,args)), (ypos,APPLY(head',args')) -> (
      if head <> head' then raise TermEquivalenceFailure;
      let t = head_to_type env xpos head in
      let rec repeat t args_passed args args' =
	if !debug_mode then printf " path_equivalence repeat, head type = %a, args_passed = %a\n\targs = %a\n\targs' = %a\n%!" _t t _s args_passed _s args _s args';
        match t,args,args' with
        | (pos,F_Pi(v,a,b)), ARG(x,args), ARG(y,args') ->
            term_equivalence env x y a;
	    let b' = subst_type (v,x) b in
            repeat b' (ARG(x,args_passed)) args args'
        | (pos,F_Sigma(v,a,b)), CAR args, CAR args' -> 
	    let args_passed' = CAR args_passed in
	    repeat a args_passed' args args'
        | (pos,F_Sigma(v,a,b)), CDR args, CDR args' -> 
	    let b' = subst_car_passed_term v pos head args_passed b in
	    let args_passed' = CDR args_passed in
	    repeat b' args_passed' args args'
        | t, END, END -> t
        | _ -> 
	    if !debug_mode then printf " path_equivalence failure\n%!";
	    raise TermEquivalenceFailure
      in repeat t END args args')
  | _  -> 
      if !debug_mode then printf " path_equivalence failure\n%!";
      raise TermEquivalenceFailure) in
  if !debug_mode then printf " path_equivalence okay, type = %a\n%!" _t t;
  t

and type_equivalence (env:context) (t:lf_type) (u:lf_type) : unit =
  (* see figure 11, page 711 [EEST] *)
  (* assume t and u have already been verified to be types *)
  if !debug_mode then printf " type_equivalence\n\t t=%a\n\t u=%a\n%!" _t t _t u;
  if try_alpha && Alpha.UEqual.type_equiv empty_uContext t u then () else
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  try
    match t0, u0 with
    | F_Singleton a, F_Singleton b ->
        let (x,t) = strip_singleton a in
        let (y,u) = strip_singleton b in
        type_equivalence env t u;
        term_equivalence env x y t
    | F_Sigma(v,a,b), F_Sigma(w,c,d)
    | F_Pi(v,a,b), F_Pi(w,c,d) ->
        type_equivalence env a c;
        let x = newfresh v in
        let b = subst_type (v, var_to_lf x) b in
        let d = subst_type (w, var_to_lf x) d in
        let env = (x, a) :: env in
        type_equivalence env b d
    | F_Apply(h,args), F_Apply(h',args') ->
        (* Here we augment the algorithm in the paper to handle the type families of LF. *)
        if not (h = h') then raise TypeEquivalenceFailure;
        let k = tfhead_to_kind h in
        let rec repeat (k:lf_kind) args args' : unit =
          match k,args,args' with
          | K_Pi(v,t,k), x :: args, x' :: args' ->
              term_equivalence env x x' t;
              repeat (subst_kind (v,x) k) args args'
          | ( K_expression | K_judgment | K_judged_expression | K_judged_expression_judgment ), [], [] -> ()
          | _ -> internal ()
        in repeat k args args'
    | _ -> raise TypeEquivalenceFailure
  with TermEquivalenceFailure -> raise TypeEquivalenceFailure

and subtype (env:context) (t:lf_type) (u:lf_type) : unit =
  (* assume t and u have already been verified to be types *)
  (* driven by syntax *)
  (* see figure 12, page 715 [EEST] *)
  if !debug_mode then printf " subtype\n\t t=%a\n\t u=%a\n%!" _t t _t u;
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  try
    match t0, u0 with
    | F_Singleton a, F_Singleton b ->
        let (x,t) = strip_singleton a in
        let (y,u) = strip_singleton b in
        type_equivalence env t u;
        term_equivalence env x y t
    | _, F_Singleton _ -> raise SubtypeFailure
    | F_Singleton a, _ -> 
        let (x,t) = strip_singleton a in
        subtype env t u
    | F_Pi(x,a,b) , F_Pi(y,c,d) ->
        subtype env c a;                        (* contravariant *)
        let w = newfresh (Var "w") in
        subtype ((w, c) :: env) (subst_type (x,var_to_lf w) b) (subst_type (y,var_to_lf w) d)
    | F_Sigma(x,a,b) , F_Sigma(y,c,d) ->
        subtype env a c;                        (* covariant *)
        let w = newfresh (Var "w") in
        subtype ((w, a) :: env) (subst_type (x,var_to_lf w) b) (subst_type (y,var_to_lf w) d)
    | _ -> type_equivalence env (tpos,t0) (upos,u0)
  with TypeEquivalenceFailure -> raise SubtypeFailure

let rec is_product_type env t = 
  match unmark t with 
  | F_Pi _ -> true
  | F_Singleton(_,t) -> is_product_type env t
  | F_Sigma _ -> false
  | F_Apply _ -> false    

let rec type_check (surr:surrounding) (env:context) (e0:lf_expr) (t:lf_type) : lf_expr = 
  (* assume t has been verified to be a type *)
  (* see figure 13, page 716 [EEST] *)
  (* we modify the algorithm to return a possibly modified expression e, with holes filled in by tactics *)
  (* We hard code this tactic:
       Fill in holes of the form [ ([ev] f o _) ] by using [tau] to compute the type that ought to go there. *)
  let pos = get_pos t in 
  match unmark e0, unmark t with
  | APPLY(TAC tac,args), _ -> (
      let pos = get_pos e0 in 
      match apply_tactic surr env pos t tac with
      | TacticSuccess suggestion -> 
          let suggestion = apply_args suggestion args in
          type_check surr env suggestion t
      | TacticFailure ->
          raise (TypeCheckingFailure (env, [
                               pos, "tactic failed : "^tactic_to_string tac;
                               pos, "in hole of type: "^lf_type_to_string t])))

  | LAMBDA(v,body), F_Pi(w,a,b) -> (* the published algorithm is not applicable here, since
                                   our lambda doesn't contain type information for the variable,
                                   and theirs does *)
      let surr = (None,e0,Some t) :: surr in
      let body = type_check surr ((v,a) :: env) body (subst_type (w,var_to_lf v) b) in
      pos, LAMBDA(v,body)
  | LAMBDA _, _ -> mismatch_term_type env e0 t
 
  | _, F_Sigma(w,a,b) -> (* The published algorithm omits this, correctly, but we want to
                            give advice to tactics for filling holes in [p], so we try type-directed
                            type checking as long as possible. *)
      let (x,y) = (pi1 e0,pi2 e0) in
      let x = type_check [(Some 0,e0,Some t)] env x a in
      let b = subst_type (w,x) b in
      let y = type_check [(Some 1,e0,Some t)] env y b in
      pos, CONS(x,y)

  | _, _  ->
      let (e,s) = type_synthesis surr env e0 in 
      if !debug_mode then printf " type_check\n\t e = %a\n\t s = %a\n\t t = %a\n%!" _e e _t s _t t;
      try
        subtype env s t;
        e
      with SubtypeFailure -> 
	mismatch_term_type_type env e0 s t

and type_synthesis (surr:surrounding) (env:context) (m:lf_expr) : lf_expr * lf_type =
  (* assume nothing *)
  (* see figure 13, page 716 [EEST] *)
  (* return a pair consisting of the original expression with any tactic holes filled in, 
     and the synthesized type *)
  let pos = get_pos m in
  match unmark m with
  | LAMBDA _ -> err env pos ("function has no type: " ^ lf_expr_to_string m)
  | CONS(x,y) ->
      let x',t = type_synthesis surr env x in
      let y',u = type_synthesis surr env y in (pos,CONS(x',y')), (pos,F_Sigma(newunused(),t,u))
  | APPLY(head,args) ->
      match head with
      | TAC _ -> err env pos "tactic found in context where no type advice is available"
      | _ -> ();
      let head_type = head_to_type env pos head in
      let args_passed = END in            (* we retain the arguments we've passed as a spine in reverse order *)
      let rec repeat i env head_type args_passed args = (
        match unmark head_type, args with
        | F_Pi(v,a',a''), ARG(m',args') ->
            let surr = (Some i,m,None) :: surr in 
            let env = apply_ts_binder env i m in
            let m' = type_check surr env m' a' in
            let (args'',u) = repeat (i+1) env (subst_type (v,m') a'') (ARG(m',args_passed)) args' in
            ARG(m',args''), u
        | F_Singleton(e,t), args -> repeat i env t args_passed args
        | F_Sigma(v,a,b), CAR args ->
            let (args',t) = repeat (i+1) env a (CAR args_passed) args in
            (CAR args', t)
        | F_Sigma(v,a,b), CDR args -> 
            let b' = subst_car_passed_term v pos head args_passed b in 
            let (args',t) = repeat (i+1) env b' (CDR args_passed) args in
            (CDR args', t)
        | t, END -> END, (pos,t)
        | _, ARG(arg,_) -> err env (get_pos arg) "extra argument"
        | _, CAR _ -> err env pos ("pi1 expected a pair (3) but got " ^ lf_expr_to_string (with_pos pos (APPLY(head,reverse_spine args_passed))))
        | _, CDR _ -> err env pos "pi2 expected a pair (3)"
       )
      in
      let (args',t) = repeat 0 env head_type args_passed args in
      let e = pos, APPLY(head,args') in
      let t = with_pos_of t (F_Singleton(e,t)) in (* this isn't quite like the algorithm in the paper, but it seems to work *)
      e,t

let type_validity (env:context) (t:lf_type) : lf_type =
  (* assume the kinds of constants, and the types in them, have been checked *)
  (* driven by syntax *)
  (* return the same type t, but with tactic holes replaced *)
  (* see figure 12, page 715 [EEST] *)
  let rec type_validity env t =
    let (pos,t) = t 
    in 
    ( pos,
      match t with 
      | F_Pi(v,t,u) ->
          let t = type_validity env t in
          let u = type_validity ((v,t) :: env) u in
          F_Pi(v,t,u)
      | F_Sigma(v,t,u) ->
          let t = type_validity env t in
          let u = type_validity ((v,t) :: env) u in
          F_Sigma(v,t,u)
      | F_Apply(head,args) ->
          let kind = tfhead_to_kind head in
          let rec repeat env kind (args:lf_expr list) = 
            match kind, args with 
            | ( K_expression | K_judgment | K_judged_expression | K_judged_expression_judgment ), [] -> []
            | ( K_expression | K_judgment | K_judged_expression | K_judged_expression_judgment ), x :: args -> err env pos "at least one argument too many";
            | K_Pi(v,a,kind'), x :: args -> 
                let x' = type_check [] env x a in
                x' :: repeat env (subst_kind (v,x') kind') args
            | K_Pi(_,a,_), [] -> errmissingarg env pos a
          in 
          let args' = repeat env kind args in
          F_Apply(head,args')
      | F_Singleton(x,t) -> 
          let t = type_validity env t in
          let x = type_check [] env x t in                (* rule 46 *)
          F_Singleton(x,t)) in
  try
    type_validity env t
  with TypeCheckingFailure(env,ps) ->
    raise (TypeCheckingFailure(
           env,
           ps @ [ (get_pos t, "while checking validity of type\n\t" ^ lf_type_to_string t) ]))

let type_synthesis = type_synthesis []

let type_check = type_check []


(** Normalization routines. *)

(* We may wish to put the normalization routines in another file. *)

let rec num_args t = match unmark t with 
  | F_Pi(_,_,b) -> 1 + num_args b
  | _ -> 0

let rec term_normalization (env:context) (x:lf_expr) (t:lf_type) : lf_expr =
  (* see figure 9 page 696 [EEST] *)
  let (pos,t0) = t in
  match t0 with 
  | F_Pi(v,a,b) ->
      let w = newfresh v in		(* in case x contains v as a free variable *)
      let w' = var_to_lf w in 
      let b = subst_type (v,w') b in
      let env = (w,a) :: env in
      let result = apply_args x (ARG(w',END)) in
      let body = term_normalization env result b in
      pos, LAMBDA(v,body)
  | F_Sigma(v,a,b) ->
      let pos = get_pos x in
      let p = x in
      let x = pi1 p in
      let y = pi2 p in
      let x = term_normalization env x a in
      let b = subst_type (v,x) b in
      let y = term_normalization env y b in
      pos, CONS(x,y)
  | F_Apply _
  | F_Singleton _ ->
      let x = head_normalization env x in
      let (x,t) = path_normalization env x in
      x
      
and path_normalization (env:context) (x:lf_expr) : lf_expr * lf_type =
  (* returns the normalized term x and the inferred type of x *)
  (* see figure 9 page 696 [EEST] *)
  (* assume x is head normalized *)
  if !debug_mode then printf " path_normalization entering with x=%a\n%!" _e x;
  let pos = get_pos x in
  match unmark x with
  | LAMBDA _ -> err env pos "path_normalization encountered a function"
  | CONS _ -> err env pos "path_normalization encountered a pair"
  | APPLY(head,args) -> (
      if !debug_mode then printf "\thead=%a args=%a\n%!" _h head _s args;
      let t0 = head_to_type env pos head in
      let (t,args) =
        let args_passed = END in          (* we store the arguments we've passed in reverse order *)
        let rec repeat t args_passed args : lf_type * spine = (
	  if !debug_mode then printf " path_normalization repeat\n\tt=%a\n\targs_passed=%a\n\targs=%a\n%!" _e x _s args_passed _s args;
          match unmark t with
          | F_Pi(v,a,b) -> (
              match args with
              | END -> raise (TypeCheckingFailure (env, [
                                                    pos , "expected "^string_of_int (num_args t)^" more arguments";
                                                    (get_pos t0), (" using:\n\t"^lf_head_to_string head^" : "^lf_type_to_string t0)]))
              | CAR args -> err env pos "pi1 expected a pair (4)"
              | CDR args -> err env pos "pi2 expected a pair (4)"
              | ARG(x, args) ->
                  let b = subst_type (v,x) b in
                  let x = term_normalization env x a in
                  let (c,args) = repeat b (ARG(x,args_passed)) args in
                  (c, ARG(x,args)))
          | F_Singleton _ -> 
	      if !debug_mode then printf "\tbad type t = %a\n%!" _t t;
	      print_context (Some 5) stdout env;
	      internal () (* x was head normalized, so any definition of head should have been unfolded *)
          | F_Sigma(v,a,b) -> (
              match args with 
              | END -> (t,END)
              | CAR args -> 
                  let (c,args) = repeat a (CAR args_passed) args in
                  (c, CAR args)
              | CDR args -> 
                  let b = subst_car_passed_term v pos head args_passed b in
                  let (c,args) = repeat b (CDR args_passed) args in
                  (c, CDR args)
              | ARG(x,_) -> err env (get_pos x) "unexpected argument")
          | F_Apply _ -> (
              match args with
              | END -> (t,END)
              | CAR args -> err env pos "pi1 expected a pair (5)"
              | CDR args -> err env pos "pi2 expected a pair (5)"
              | ARG(x,args) -> err env (get_pos x) "unexpected argument"))
        in repeat t0 args_passed args
      in ((pos,APPLY(head,args)), t))

let rec type_normalization (env:context) (t:lf_type) : lf_type =
  (* see figure 9 page 696 [EEST] *)
  let (pos,t0) = t in
  let t = match t0 with
  | F_Pi(v,a,b) -> 
      let a' = type_normalization env a in
      let b' = type_normalization ((v,a) :: env) b in
      F_Pi(v,a',b')
  | F_Sigma(v,a,b) -> 
      let a' = type_normalization env a in
      let b' = type_normalization ((v,a) :: env) b in
      F_Sigma(v,a',b')
  | F_Apply(head,args) ->
      let kind = tfhead_to_kind head in
      let args =
        let rec repeat env kind (args:lf_expr list) = 
          match kind, args with 
          | ( K_expression | K_judgment | K_judged_expression | K_judged_expression_judgment ), [] -> []
          | ( K_expression | K_judgment | K_judged_expression | K_judged_expression_judgment ), x :: args -> err env pos "too many arguments"
          | K_Pi(v,a,kind'), x :: args ->
              term_normalization env x a ::
              repeat ((v,a) :: env) kind' args
          | K_Pi(_,a,_), [] -> errmissingarg env pos a
        in repeat env kind args
      in F_Apply(head,args)
  | F_Singleton(x,t) -> 
      F_Singleton( term_normalization env x t, type_normalization env t )
  in (pos,t)

(* 
  Local Variables:
  compile-command: "make lfcheck.cmo "
  End:
 *)
