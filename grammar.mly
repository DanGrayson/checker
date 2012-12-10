%{ 
open Error
open Variables
open Typesystem
open Names
open Helpers
open Definitions
%}
%start command ts_exprEof
%type <Toplevel.command> command
%type <Typesystem.atomic_expr> ts_exprEof ts_expr
%type <Typesystem.unmarked_atomic_expr> unmarked_ts_expr
%type <Typesystem.lf_expr list> arglist
%type <Typesystem.lf_type> lf_type
%type <Typesystem.lf_expr> lf_expr lf_expr_from_ts_syntax
%token <int> NUMBER
%token <string> IDENTIFIER CONSTANT CONSTANT_SEMI
%token <Variables.var> VARIABLE
%token

  Wlparen Wrparen Wrbracket Wlbracket Wcomma Wperiod Colon Wstar Arrow
  ArrowFromBar Wequal Colonequal Wunderscore WRule Wgreaterequal Wgreater
  Wlessequal Wless Semicolon KUlevel Kumax KType Ktype KPi Klambda KSigma
  WCheck WDefine WShow WEnd WVariable WAlpha Weof WCheckUniverses Wtilde
  KSingleton Axiom Wdollar W_LF W_TS Kpair Kpi1 Kpi2 Wtimes DoubleBackslash
  Turnstile DoubleArrow DoubleColon Backslash DoubleArrowFromBar
  DoubleSemicolon DoubleStar

  ReduceFunctionType ReduceProductType

/* precedences, lowest first */

%nonassoc

  Reduce_command

%right

  /* we want [lambda x, lambda y, b] to be [lambda x, (lambda y, b)] */
  /* we want [lambda x, f b] to be [lambda x, (f b)] */
  Reduce_binder

%nonassoc

  /* we want  [*f x] to be [*(f x)]  and  [*x->y] to be [( *x )->y]  */
  Reduce_star

%right

  /* function type */
  /* we want [a -> b -> c] to be [a -> (b -> c)] */
  ReduceFunctionType
  Arrow

%right

  /* product type */
  /* we want [a * b * c] to be [a * (b * c)], by analogy with [a -> b] */
  /* we want [a * b -> c] to be [(a * b) -> c]
  ReduceProductType
  Wtimes

%right

  /* substitution */
  /* we want [x\\y\\f] to be [x\\(y\\f)] */
  DoubleBackslash

%nonassoc

  /* We want [f x IDENTIFIER] to reduce to [(f x) IDENTIFIER], so
     the precedence of IDENTIFIER is lower than Reduce_application. */

  IDENTIFIER

  /* These are the other tokens that can begin a TS-expression : ditto. */

  Wunderscore Wlparen Kumax CONSTANT_SEMI CONSTANT Wstar
  Klambda KSigma KPi VARIABLE

%left

  Reduce_application

%%

lf_type:
| t=bare_lf_type
    { Position($startpos, $endpos), t}
| Wlparen t=lf_type Wrparen 
    { t }

bare_lf_type:
| f=lf_type_constant args=list(lf_expr)
    { F_APPLY(f,args) }
| KPi v=bare_variable Colon a=lf_type Wcomma b=lf_type
    %prec Reduce_binder
    { F_Pi(v,a,b) }
| KSigma v=bare_variable Colon a=lf_type Wcomma b=lf_type
    %prec Reduce_binder
    { F_Sigma(v,a,b) }
| Wlparen v=bare_variable Colon a=lf_type Wrparen Wtimes b=lf_type
    %prec ReduceProductType
    { F_Sigma(v,a,b) }
| a=lf_type Wtimes b=lf_type (*??*)
    %prec ReduceProductType
    { F_Sigma(newunused(),a,b) }
| Wlparen v=bare_variable Colon a=lf_type Wrparen Arrow b=lf_type
   %prec ReduceFunctionType
   { F_Pi(v,a,b) }
| a=lf_type Arrow b=lf_type
   %prec ReduceFunctionType
   { F_Pi(newunused(),a,b) }
| KSingleton Wlparen x=lf_expr Colon t=lf_type Wrparen
    { F_Singleton(x,t) }
| Wlbracket a=lf_expr Ktype Wrbracket
    { F_APPLY(F_istype, [a]) }
| Wlbracket a=lf_expr Colon b=lf_expr Wrbracket
    { F_APPLY(F_hastype, [a;b]) }
| Wlbracket a=lf_expr Wequal b=lf_expr Colon c=lf_expr Wrbracket
    { F_APPLY(F_object_equality, [a;b;c]) }
| Wlbracket a=lf_expr Wequal b=lf_expr Wrbracket
    { F_APPLY(F_type_equality, [a;b]) }

| Wlbracket a=lf_expr Wtilde b=lf_expr Colon KType Wrbracket
    { F_APPLY(F_type_uequality, [a;b]) }
| Wlbracket a=lf_expr Wtilde b=lf_expr Wrbracket
    { F_APPLY(F_object_uequality, [a;b]) }

lf_type_constant:
| l=IDENTIFIER 
    { 
      try List.assoc l Names.string_to_type_constant
      with 
        Not_found ->
          Printf.fprintf stderr "%s: unknown type constant %s\n" 
            (errfmt (Position($startpos, $endpos)))
            l;
          flush stderr;
          $syntaxerror
    }

lf_expr:
| e=atomic_term
    { CAN(Position($startpos, $endpos), e)  }
| e=lf_lambda_expression
    { e }
| Kpair a=lf_expr b=lf_expr
    { PAIR(Position($startpos, $endpos), a, b) }
| Kpi1 a=lf_expr
    { CAN(Position($startpos, $endpos), PR1 a) }
| Kpi2 a=lf_expr
    { CAN(Position($startpos, $endpos), PR2 a) }

lf_lambda_expression:

| Wgreater body=lf_expr
    { LAMBDA(newunused(),body) }

| Wlparen Klambda v=variable Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }
| Wlparen Klambda v=variable_unused Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }

| Wlparen v=variable ArrowFromBar body=lf_lambda_expression_body Wrparen
    { LAMBDA(v,body) }
| Wlparen v=variable_unused ArrowFromBar body=lf_lambda_expression_body Wrparen
    { LAMBDA(v,body) }

lf_lambda_expression_body:
| e=lf_expr
    { e }
| v=variable ArrowFromBar body=lf_lambda_expression_body
    { LAMBDA(v,body) }
| v=variable_unused ArrowFromBar body=lf_lambda_expression_body
    { LAMBDA(v,body) }

variable_unused:
| Wunderscore
    { newunused() }

tactic_descriptor:
| c=IDENTIFIER
  { c }

tactic_expr:
| Wdollar name=tactic_descriptor
    { TacticHole (Q_name name) }
| Wdollar index=NUMBER
    { TacticHole (Q_index index) }

atomic_term:
| tac= tactic_expr
    {tac}
| bare_variable
    { APPLY(V $1,[]) }
| Wunderscore
    { new_hole () }
| Wlparen f=lf_expr_head args=list(lf_expr) Wrparen
    { APPLY(f,args) }

lf_expr_head:
| tsterm_head
    { $1 }
| bare_variable
    { V $1 }

command: c=command0 
  { Position($startpos, $endpos), c }

command0:
| Weof
    { raise Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Colon KType Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Colon KUlevel eqns=preceded(Semicolon,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }

| Axiom W_TS v=IDENTIFIER Colon t=ts_expr Wperiod
    { Toplevel.AxiomTS(v,t) }
| Axiom W_LF v=IDENTIFIER Colon t=lf_type Wperiod
    { Toplevel.AxiomLF(v,t) }
| WRule num=separated_nonempty_list(Wperiod,NUMBER) name=IDENTIFIER Colon t=lf_type Wperiod
    { Toplevel.Rule (num,name,t) }

| WCheck W_LF e=lf_expr Wperiod
    { Toplevel.CheckLF e }
| WCheck W_LF Ktype e=lf_type Wperiod
    { Toplevel.CheckLFtype e }
| WCheck W_TS o=ts_expr Wperiod
    { Toplevel.CheckTS o }
| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }
| WAlpha e1=ts_expr Wequal e2=ts_expr Wperiod
    { Toplevel.Alpha (e1, e2) }

| WDefine name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t, Some d1) }
| WDefine name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr Semicolon d1=ts_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t, Some (CAN d1)) }
| WDefine name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t, None) }

| WDefine name=IDENTIFIER parms=parmList Colonequal t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { Toplevel.TDefinition (name, parms, t, Some d1) }
| WDefine name=IDENTIFIER parms=parmList Colonequal t=ts_expr Semicolon d1=ts_expr Wperiod 
    { Toplevel.TDefinition (name, parms, t, Some (CAN d1)) }
| WDefine name=IDENTIFIER parms=parmList Colonequal t=ts_expr Wperiod 
    { Toplevel.TDefinition (name, parms, t, None) }

| WDefine name=IDENTIFIER parms=parmList Colonequal t1=ts_expr Wequal t2=ts_expr Wperiod 
    { Toplevel.TeqDefinition (name, parms, t1, t2) }

| WDefine name=IDENTIFIER parms=parmList Colonequal o1=ts_expr Wequal o2=ts_expr Colon t=ts_expr Wperiod 
    { Toplevel.OeqDefinition (name, parms, o1, o2, t) }

| WShow Wperiod 
    { Toplevel.Show None }
| WShow n=NUMBER Wperiod 
    { Toplevel.Show (Some n) }
| WEnd Wperiod
    { Toplevel.End }

uParm: vars=nonempty_list(IDENTIFIER) Colon KUlevel eqns=preceded(Semicolon,uEquation)*
    { UParm (UContext ((List.map make_Var vars),eqns)) }
tParm: vars=nonempty_list(IDENTIFIER) Colon KType 
    { TParm (List.map make_Var vars) }
oParm: vars=nonempty_list(IDENTIFIER) Colon t=ts_expr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=ts_expr Wequal v=ts_expr 
    { (u,v) }
| v=ts_expr Wgreaterequal u=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ CAN u; CAN v])), v }
| u=ts_expr Wlessequal v=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ CAN u; CAN v])), v }
| v=ts_expr Wgreater u=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ CAN (Position($startpos, $endpos), APPLY( U U_next,[CAN u])); CAN v])), v }
| u=ts_expr Wless v=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ CAN (Position($startpos, $endpos), APPLY( U U_next,[CAN u])); CAN v])), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

ts_exprEof: a=ts_expr Weof {a}

variable:
| bare_variable
    { $1 }

variable_or_unused:
| bare_variable_or_unused
    { $1 }

lf_expr_from_ts_syntax:
| tac= tactic_expr
    { CAN (Position($startpos, $endpos), tac) }
| e = ts_expr
    { CAN e }
| v=variable DoubleArrowFromBar body=lf_expr_from_ts_syntax
    { LAMBDA(v,body) }
| v=variable_unused DoubleArrowFromBar body=lf_expr_from_ts_syntax
    { LAMBDA(v,body) }
| o=lf_expr_from_ts_syntax DoubleBackslash f=lf_expr_from_ts_syntax
    { Substitute.apply_args (Position($startpos, $endpos)) f [o] }

ts_expr:
| unmarked_ts_expr
    { (Position($startpos, $endpos), $1) }
| parenthesized(ts_expr) 
    {$1}

tsterm_head:
| name=CONSTANT
    { try List.assoc name Names.lf_expr_head_strings with Not_found -> V (Var name) }

arglist:
| Wlparen a=separated_list(Wcomma,lf_expr_from_ts_syntax) Wrparen
    {a}

bare_variable:
| IDENTIFIER
    { Var $1 }
| v=VARIABLE
    { v }

bare_variable_or_unused:
| v=bare_variable
    {v}
| v=variable_unused
    {v}

unmarked_ts_expr:
| bare_variable
    { APPLY(V $1,[]) }
| Wunderscore
    { new_hole () }
| f=ts_expr o=ts_expr
    %prec Reduce_application
    { APPLY(O O_ev, [CAN f; CAN o; CAN(Position($startpos, $endpos), (TacticHole (Q_name "ev3")))]) }
| Klambda x=variable Colon t=ts_expr Wcomma o=ts_expr
    %prec Reduce_binder
    { make_OO_lambda t (x,o) }
| Wstar o=ts_expr
    %prec Reduce_star
    { make_TT_El o }
| KPi x=variable Colon t1=ts_expr Wcomma t2=ts_expr
    %prec Reduce_binder
    { make_TT_Pi t1 (x,t2) }
| Wlparen x=variable Colon t=ts_expr Wrparen Arrow u=ts_expr
    { make_TT_Pi t (x,u) }
| t=ts_expr Arrow u=ts_expr
    { make_TT_Pi t (newunused(),u) }
| KSigma x=variable Colon t1=ts_expr Wcomma t2=ts_expr
    %prec Reduce_binder
    { make_TT_Sigma t1 (x,t2) }
| Kumax Wlparen u=ts_expr Wcomma v=ts_expr Wrparen
    { APPLY(U U_max,[CAN u;CAN v])  }
| label=tsterm_head args=arglist
    {
     match label with
     | V _ -> APPLY(label,args)
     | _ -> (
         match head_to_vardist label with
         | None -> APPLY(label,args)
         | Some (n,_) ->
             if n = 0 then APPLY(label,args)
             else
               raise (MarkedError
                        ( Position($startpos, $endpos),
                          "expected " ^ string_of_int n ^ " variable" ^ if n != 1 then "s" else "")))
   }
| name=CONSTANT_SEMI vars=separated_list(Wcomma,variable_or_unused) Wrbracket args=arglist
    {
     let label = 
       try List.assoc name Names.lf_expr_head_strings
       with Not_found -> 
         Printf.fprintf stderr "%s: unknown term constant [%s]\n" 
           (errfmt (Position($startpos, $endpos)))
           name;
         flush stderr;
         $syntaxerror
     in
     match head_to_vardist label with
     | None -> raise (MarkedError (Position($startpos, $endpos), "expected no variables"))
     | Some (nvars,varindices) ->
         if nvars != List.length vars then
           raise (MarkedError
                    ( Position($startpos, $endpos),
                      "expected " ^ string_of_int nvars ^ " variable" ^ if nvars != 1 then "s" else ""));
         let nargs = List.length varindices
         in
         if List.length args != nargs then
           raise (MarkedError
                    ( Position($startpos, $endpos),
                      "expected " ^ string_of_int nargs ^ " argument" ^ if nargs != 1 then "s" else ""));
         let args = List.map2 (
           fun indices arg ->
             (* example: indices = [0;1], change arg to (LAMBDA v_0, (LAMBDA v_1, arg)) *)
             List.fold_right (
             fun index arg -> LAMBDA( List.nth vars index, arg)
                 ) indices arg
          ) varindices args
         in
         APPLY(label,args)
   }
 
