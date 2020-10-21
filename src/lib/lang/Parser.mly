%{
  open Syntax
  open ProbNv_datastructures
  open Collections
  open Batteries

  let exp ?ty:(ty=None) e span : exp = aexp (e, ty, span)

  let value ?ty:(ty=None) v span : value = avalue (v, ty, span)

  let to_value v span : exp = exp (e_val (value v span)) span

  (* TODO: span not calculated correctly here? *)
  let rec make_fun params (body : exp) (body_span: ProbNv_datastructures.Span.t) (span : ProbNv_datastructures.Span.t) : exp =
    match params with
    | [] -> body
    | (x,tyopt)::rest ->
        let e = efun {arg=x; argty=tyopt; resty=None; body=make_fun rest body body_span body_span; fmode = None} in
        exp e span

  let local_let (id,params) body body_span span =
    (id, make_fun params body body_span span)

  let global_let (id,params) body body_span span =
    let e = make_fun params body body_span span in
    DLet (id, e)


  let ip_to_dec b1 b2 b3 b4 =
    let b1 = ProbNv_datastructures.Integer.to_int b1 in
    let b2 = ProbNv_datastructures.Integer.to_int b2 in
    let b3 = ProbNv_datastructures.Integer.to_int b3 in
    let b4 = ProbNv_datastructures.Integer.to_int b4 in
    if (b1 > 255) || (b2 > 255) || (b3 > 255) || (b4 > 255) then
      failwith "Invalid ip address"
    else
      (b1 * 16777216) + (b2 * 65536) + (b3 * 256) + b4
      |> ProbNv_datastructures.Integer.of_int

  let make_dsolve ?ty:(ty=None) x init trans merge =
    DSolve ({aty = ty; var_names = evar x; init; trans; merge})


  let ensure_node_pattern p =
    match p with
    | PInt n -> PNode (ProbNv_datastructures.Integer.to_int n)
    | _ -> p

  let tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> PTuple ps

   let tuple_it es (span : Span.t) : exp =
    match es with
    | [e] -> exp e span
    | es -> exp (etuple es) span

%}


%token <ProbNv_datastructures.Span.t * ProbNv_datastructures.Var.t> ID
%token <ProbNv_datastructures.Span.t * ProbNv_datastructures.Integer.t> NUM
%token <ProbNv_datastructures.Span.t * int> NODE
%token <ProbNv_datastructures.Span.t> AND
%token <ProbNv_datastructures.Span.t> OR
%token <ProbNv_datastructures.Span.t> NOT
%token <ProbNv_datastructures.Span.t> TRUE
%token <ProbNv_datastructures.Span.t> FALSE
%token <ProbNv_datastructures.Span.t * int> PLUS
%token <ProbNv_datastructures.Span.t * int> UAND
%token <ProbNv_datastructures.Span.t> EQ
%token <ProbNv_datastructures.Span.t * int> SUB
%token <ProbNv_datastructures.Span.t * int> LESS
%token <ProbNv_datastructures.Span.t * int> GREATER
%token <ProbNv_datastructures.Span.t * int> LEQ
%token <ProbNv_datastructures.Span.t * int> GEQ
%token <ProbNv_datastructures.Span.t> NGEQ
%token <ProbNv_datastructures.Span.t> NGREATER
%token <ProbNv_datastructures.Span.t> NLESS
%token <ProbNv_datastructures.Span.t> NLEQ
%token <ProbNv_datastructures.Span.t> LET
%token <ProbNv_datastructures.Span.t> IN
%token <ProbNv_datastructures.Span.t> IF
%token <ProbNv_datastructures.Span.t> THEN
%token <ProbNv_datastructures.Span.t> ELSE
%token <ProbNv_datastructures.Span.t> FUN
%token <ProbNv_datastructures.Span.t> SOME
%token <ProbNv_datastructures.Span.t> NONE
%token <ProbNv_datastructures.Span.t> MATCH
%token <ProbNv_datastructures.Span.t> WITH
%token <ProbNv_datastructures.Span.t> BAR
%token <ProbNv_datastructures.Span.t> ARROW
%token <ProbNv_datastructures.Span.t> DOT
%token <ProbNv_datastructures.Span.t> SLASH
%token <ProbNv_datastructures.Span.t> SEMI
%token <ProbNv_datastructures.Span.t> LPAREN
%token <ProbNv_datastructures.Span.t> RPAREN
%token <ProbNv_datastructures.Span.t> LBRACKET
%token <ProbNv_datastructures.Span.t> RBRACKET
%token <ProbNv_datastructures.Span.t> LBRACE
%token <ProbNv_datastructures.Span.t> RBRACE
%token <ProbNv_datastructures.Span.t> COMMA
%token <ProbNv_datastructures.Span.t> TILDE
%token <ProbNv_datastructures.Span.t> UNDERSCORE
%token <ProbNv_datastructures.Span.t> TOPTION
%token <ProbNv_datastructures.Span.t> SOLUTION
%token <ProbNv_datastructures.Span.t> ASSERT
%token <ProbNv_datastructures.Span.t> TYPE
%token <ProbNv_datastructures.Span.t> COLON
%token <ProbNv_datastructures.Span.t> TBOOL
%token <ProbNv_datastructures.Span.t> TNODE
%token <ProbNv_datastructures.Span.t> TEDGE
%token <ProbNv_datastructures.Span.t * int> TINT
%token <ProbNv_datastructures.Span.t> EDGES
%token <ProbNv_datastructures.Span.t> NODES
%token <ProbNv_datastructures.Span.t> SYMBOLIC
%token <ProbNv_datastructures.Span.t> MINUS
%token <ProbNv_datastructures.Span.t> SYMB
%token <ProbNv_datastructures.Span.t> MULTI
%token <ProbNv_datastructures.Span.t> CONCRETE


%token EOF

%start prog
%type  <Syntax.declarations> prog

%start expreof
%type <Syntax.exp> expreof

%right ELSE IN     /* lowest precedence */
%right ARROW
%left AND OR
%nonassoc GEQ GREATER LEQ LESS EQ 
%left PLUS SUB UAND MINUS
%right NOT
%right SOME
%nonassoc DOT
%left LBRACKET      /* highest precedence */

%%


mode:
   | CONCRETE { Concrete }
   | SYMB     { Symbolic }
   | MULTI    { Multivalue }

bty:
   | TBOOL                              { TBool }
   | TNODE                              { TNode }
   | TEDGE                              { TEdge }
   | TINT                               { Syntax.TInt (snd $1) }
   | LPAREN tys RPAREN                  { if List.length $2 = 1 then failwith "impossible" else TTuple $2 }
   /*| TOPTION LBRACKET ty RBRACKET       { TOption $3 }
   | TDICT LBRACKET ty COMMA ty RBRACKET{ TMap ($3,$5) } */
   /* | TSET LBRACKET ty RBRACKET          { TMap ($3,TBool) }
   | LBRACE record_entry_tys RBRACE     { TRecord (make_record_map $2) }
   | ID                                 { get_user_type (snd $1) } */
;

ty:
  | ty ARROW ty     { {typ=TArrow ($1,$3); mode= Some Concrete} }
  | LPAREN ty RPAREN                  { $2 }  
  | LBRACKET mode RBRACKET bty             { {typ=$4; mode= Some $2} }

tys:
  | ty                                   { [$1] }
  | ty COMMA tys                         { $1::$3 }
;

/* record_entry_ty:
  | ID COLON ty                         { snd $1, $3 }
; */

/* record_entry_tys:
  | record_entry_ty                       { [$1] }
  | record_entry_ty SEMI                  { [$1] }
  | record_entry_ty SEMI record_entry_tys { $1::$3 } */

param:
   | ID                                 { (snd $1, None) }
   | LPAREN ID COLON ty RPAREN          { (snd $2, Some $4) }
;

params:
    | param                             { [$1] }
    | param params                      { $1::$2 }
;

letvars:
    | ID                                { (snd $1,[]) }
    | ID params                         { (snd $1, $2) }
;

component:
    /* | LET letvars EQ SOLUTION expr      { make_dsolve (fst $2) $5 } */
    | LET letvars EQ SOLUTION LPAREN expr COMMA expr COMMA expr RPAREN     { make_dsolve (fst $2) $6 $8 $10 }
    | LET letvars EQ expr               { global_let $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | SYMBOLIC ID COLON bty             { DSymbolic (snd $2, {typ = $4; mode=Some Symbolic}) }
    | ASSERT expr                       { DAssert $2 }
    | LET EDGES EQ LBRACE RBRACE        { DEdges [] }
    | LET EDGES EQ LBRACE edges RBRACE  { DEdges $5 }
    | LET NODES EQ NUM                  { DNodes (ProbNv_datastructures.Integer.to_int (snd $4)) }
    /* | TYPE ID EQ ty                     { (add_user_type (snd $2) $4; DUserTy (snd $2, $4)) } */
;

components:
    | component                         { [$1] }
    | component components              { $1 :: $2 }
;

/* record_entry_expr:
  | ID EQ expr                       { snd $1, $3 }
;

record_entry_exprs:
  | record_entry_expr                         { [$1] }
  | record_entry_expr SEMI                    { [$1] }
  | record_entry_expr SEMI record_entry_exprs { $1::$3 } */

expreof:
    expr EOF    { $1 }
;

expr:
    | LET letvars EQ expr IN expr       { let span = (Span.extend $1 $6.espan) in
                                          let (id, e) = local_let $2 $4 $4.espan span in
                                          exp (elet id e $6) span }
    /* | LET LPAREN patterns RPAREN EQ expr IN expr
                                        { let p = tuple_pattern $3 in
                                          let e = ematch $6 (addBranch p $8 emptyBranch) in
                                          let span = Span.extend $1 $8.espan in
                                          exp e span } */
    | IF expr THEN expr ELSE expr       { exp (eif $2 $4 $6) (Span.extend $1 $6.espan) }
    (* TODO: span does not include the branches here *)
    | MATCH expr WITH branches          { exp (ematch $2 $4) (Span.extend $1 $3) }
    | FUN params ARROW expr             { make_fun $2 $4 $4.espan (Span.extend $1 $4.espan) }
    /* | FOLDNODE exprsspace               { exp (eop MFoldNode $2) $1 }
    | FOLDEDGE exprsspace               { exp (eop MFoldEdge $2) $1 } */
    /* | MAP exprsspace                    { exp (eop MMap $2) $1 }
    | MAPIF exprsspace                  { exp (eop MMapFilter $2) $1 }
    | MAPITE exprsspace                 { exp (eop MMapIte $2) $1 }
    | COMBINE exprsspace                { exp (eop MMerge $2) $1 }
    | CREATEMAP exprsspace              { exp (eop MCreate $2) $1 }
    | SOME expr                         { exp (esome $2) (Span.extend $1 $2.espan) } */
    | NOT expr                          { exp (eop Not [$2]) (Span.extend $1 $2.espan) }
    | expr AND expr                     { exp (eop And [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr OR expr                      { exp (eop Or [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr PLUS expr                    { exp (eop (UAdd (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    /* | expr UAND expr                    { exp (eop (UAnd (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) } */
    | expr EQ expr                      { exp (eop Eq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr LESS expr                    { exp (eop (ULess (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GREATER expr                 { exp (eop (ULess (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr LEQ expr                     { exp (eop (ULeq (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GEQ expr                     { exp (eop (ULeq (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr NLESS expr                   { exp (eop NLess [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NGREATER expr                { exp (eop NLess [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr NLEQ expr                    { exp (eop NLeq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NGEQ expr                    { exp (eop NLeq [$3;$1]) (Span.extend $1.espan $3.espan) }
    | LPAREN expr COLON ty RPAREN       { exp ~ty:(Some $4) $2 (Span.extend $1 $5) }
    | LPAREN expr RPAREN                { exp $2 (Span.extend $1 $3) }
    /* | expr DOT ID                       { exp (eproject $1 (Var.name (snd $3))) (Span.extend ($1.espan) (fst $3)) }
    | LBRACE record_entry_exprs RBRACE  { exp (erecord (make_record_map $2)) (Span.extend $1 $3) }
    | LBRACE expr WITH record_entry_exprs RBRACE {
                                          let mk_project v =
                                          exp (eproject $2 (Var.name v)) (Span.extend $1 $3) in
                                          let lst = fill_record $4 mk_project in
                                          exp (erecord (make_record_map lst)) (Span.extend $1 $3)
                                        } */
    /* | LBRACE exprs RBRACE               { make_set $2 (Span.extend $1 $3) }
    | LBRACE RBRACE                     { make_set [] (Span.extend $1 $2) } */
    | expr2                             { $1 }
;

expr2:
    | expr2 expr3                       { exp (eapp $1 $2) (Span.extend $1.espan $2.espan) }
    | expr3                             { $1 }
;

expr3:
    | ID                                { exp (evar (snd $1)) (fst $1) }
    /* | ID DOT ID                         { exp (eproject (evar (snd $1)) (Var.name (snd $3))) (Span.extend (fst $1) (fst $3)) } */
    | NUM                               { to_value (vint (snd $1)) (fst $1) }
    | ipaddr                            { $1 }
    /* | prefixes                          { $1 } */
    | NODE                              { to_value (vnode (snd $1)) (fst $1)}
    | edge_arg TILDE edge_arg           { to_value (vedge (snd $1, snd $3)) (Span.extend (fst $1) (fst $3))}
    | TRUE                              { to_value (vbool true) $1 }
    | FALSE                             { to_value (vbool false) $1 }
    /* | NONE                              { to_value (voption None) $1 } */
    | LPAREN exprs RPAREN               { tuple_it $2 (Span.extend $1 $3) }
;

ipaddr:
  | NUM DOT NUM DOT NUM DOT NUM         { to_value (vint (ip_to_dec (snd $1) (snd $3) (snd $5) (snd $7))) (fst $1) }

/* prefixes:
  | ipaddr SLASH NUM                    { let pre = to_value (vint (ProbNv_datastructures.Integer.create ~value:(ProbNv_datastructures.Integer.to_int (snd $3)) ~size:6)) (fst $3) in
                                          etuple [$1; pre]} */

edge_arg:
  | NUM                                 { (fst $1), (ProbNv_datastructures.Integer.to_int (snd $1))}
  | NODE                                { (fst $1), (snd $1) }

exprs:
    | expr                              { [$1] }
    | expr COMMA exprs                  { $1 :: $3 }
;

edgenode:
    | NUM                               { ProbNv_datastructures.Integer.to_int (snd $1) }
    | NODE                              { snd $1 }
;

edge:
    | edgenode TILDE edgenode SEMI      { [($1, $3)] }
    | edgenode SUB edgenode SEMI        { [($1, $3)] }
    | edgenode EQ edgenode SEMI         { [($1, $3); ($3, $1)] }
;

edges:
    | edge                              { $1 }
    | edge edges                        { $1 @ $2 }
;

  pattern:
    | UNDERSCORE                        { PWild }
    | ID                                { PVar (snd $1) }
    | TRUE                              { PBool true }
    | FALSE                             { PBool false }
    | NUM                               { PInt (snd $1) }
    | NODE                              { PNode (snd $1) }
    | pattern TILDE pattern             { PEdge (ensure_node_pattern $1, ensure_node_pattern $3)}
    | LPAREN patterns RPAREN            { tuple_pattern $2 }
    /* | NONE                              { POption None }
    | SOME pattern                      { POption (Some $2) } */
    /* | LBRACE record_entry_ps RBRACE     { PRecord (make_record_map
                                          (if snd $2
                                           then fill_record (fst $2) (fun _ -> PWild)
                                           else fst $2)) } */
;

patterns:
    | pattern                           { [$1] }
    | pattern COMMA patterns            { $1::$3 }
;

/* record_entry_p:
  | ID EQ pattern                    { snd $1, $3 }
;

record_entry_ps:
  | record_entry_p                      { ([$1], false) }
  | record_entry_p SEMI                 { ([$1], false) }
  | record_entry_p SEMI UNDERSCORE      { ([$1], true) }
  | record_entry_p SEMI record_entry_ps { ($1::(fst $3), snd $3) } */

branch:
    | BAR pattern ARROW expr            { ($2, $4) }
;

branches:
    | branch                            { addBranch (fst $1) (snd $1) emptyBranch }
    | branch branches                   { addBranch (fst $1) (snd $1) $2 }
;

prog:
    | components EOF                    { $1 }
;
