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

   let make_set exprs span =
    let tru = exp (e_val (value (vbool true) span)) span in
    let rec updates e exprs =
        match exprs with
        | [] -> e
        | expr :: tl ->
            let e = exp (eop MSet [e; expr; tru]) span in
            updates e tl
    in
    let e = exp (e_val (value (vbool false) span)) span in
    let e = exp (eop MCreate [e]) span in
    updates e exprs

  let local_let (id,params) body body_span span =
    (id, make_fun params body body_span span)

  let global_let options (id,params) body body_span span =
    let e = make_fun params body body_span span in
    (* Printf.printf "%s, %s\n" (Var.to_string id) (Printing.exp_to_string e); *)
    DLet (id, e, options)


  let ip_to_dec bs =
  let bs = String.split_on_char '.' bs in
    match bs with
    | [b1; b2; b3; b4] ->
      let b1 = int_of_string b1 in
      let b2 = int_of_string b2 in
      let b3 = int_of_string b3 in
      let b4 = int_of_string b4 in
      if (b1 > 255) || (b2 > 255) || (b3 > 255) || (b4 > 255) then
        failwith "Invalid ip address"
      else
        (b1 * 16777216) + (b2 * 65536) + (b3 * 256) + b4
        |> ProbNv_datastructures.Integer.of_int
    | _ -> failwith "Invalid ip address"

  let make_dsolve ?ty:(ty=None) x f init trans merge generate =
    DSolve ({aty = ty; var_names = evar x; fib_names = evar f; init; trans; merge; generate})

  let make_dfwd x y init fwdOut fwdIn hinitV hinitE logV logE bot =
    DForward { 
      names_V = x; 
      names_E = y; 
      pty = None;
      hvty = None;
      hety = None;
      fwdInit = init;
      fwdOut = fwdOut;
      fwdIn = fwdIn;
      hinitV = hinitV;
      hinitE = hinitE;
      logE = logE;
      logV = logV;
      bot = bot; }

  let ensure_node_pattern p =
    match p with
    | PInt n -> PNode (ProbNv_datastructures.Integer.to_int n)
    | _ -> p

  let tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> PTuple ps

  let distr_tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> DistrPTuple ps

   let tuple_it es (span : Span.t) : exp =
    match es with
    | [e] -> exp e span
    | es -> exp (etuple es) span


  type user_type = Var.t (* name *) * ty (* type *)
  let user_types : user_type list ref = ref []

  let add_user_type (name : Var.t) (ty : ty) : unit =
    user_types := (name,ty)::!user_types

  let get_user_type (name : Var.t) : ty =
    match List.find_opt (fun (n,_) -> Var.equals name n) !user_types with
    | Some (_, ty) -> ty
    | None -> failwith @@ "Unknown user-defined type " ^ (Var.name name)

      let find_record_type (lab : string) : 'a StringMap.t =
    let rec aux lst =
      match lst with
      | [] -> failwith @@ "No record type using label " ^ lab
      | (_, t) :: tl ->
        match t.typ with
        | TRecord tmap ->
          if StringMap.mem lab tmap then tmap else aux tl
        | _ -> aux tl
    in
    aux !user_types

  (* Fill in a partial record specification, using the default provided for
     labels which do not already appear in the list *)
  let fill_record (lst : (Var.t * 'a) list) (default : Var.t -> 'a)
    : (Var.t * 'a) list
  =
    let record_type = find_record_type (List.hd lst |> fst |> Var.name) in
    (* FIXME: Strictly speaking, we should make sure that the elements of keys
       are a strict subset of the elements of record_type *)
    let keys = StringMap.keys record_type in
    BatEnum.fold
      (fun acc lab ->
        let lab = Var.create lab in
        match List.find_opt (fun (l,_) -> Var.equals l lab) lst with
        | None -> (lab, default lab) :: acc
        | Some elt -> elt :: acc
      ) [] keys

  let make_record_map (lst : (Var.t * 'a) list) : 'a StringMap.t =
    (* Ensure that no labels were used more than once *)
    let sorted =
      List.sort (fun (l1,_) (l2, _)-> Var.compare l1 l2) lst
    in
    let rec build_map map lst =
      match lst with
      | [] -> map
      | (l,x)::tl ->
        let l = Var.name l in
        if StringMap.mem l map
        then failwith @@ "Label used more than once in a record: " ^ l
        else build_map (StringMap.add l x map) tl
    in
    build_map StringMap.empty sorted

  let make_to_edge n1 n2 = 
    match (exp_to_value n1).v, (exp_to_value n2).v with
    | VNode n1, VNode n2 -> vedgeRaw (n1, n2)
    | _, _ -> failwith "Expected nodes"

  let edge_id = ref (-1)
%}


%token <ProbNv_datastructures.Span.t * ProbNv_datastructures.Var.t> ID
%token <ProbNv_datastructures.Span.t * ProbNv_datastructures.Integer.t> INT
%token <ProbNv_datastructures.Span.t * string> IPADDRESS
%token <ProbNv_datastructures.Span.t * float> FLOAT
%token <ProbNv_datastructures.Span.t * int> NODE
%token <ProbNv_datastructures.Span.t * string> STRING
%token <ProbNv_datastructures.Span.t> AT
%token <ProbNv_datastructures.Span.t> AND
%token <ProbNv_datastructures.Span.t> OR
%token <ProbNv_datastructures.Span.t> NOT
%token <ProbNv_datastructures.Span.t> TRUE
%token <ProbNv_datastructures.Span.t> FALSE
%token <ProbNv_datastructures.Span.t * int> PLUS
%token <ProbNv_datastructures.Span.t> FPLUS
%token <ProbNv_datastructures.Span.t> FDIV
%token <ProbNv_datastructures.Span.t> FMUL
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
%token <ProbNv_datastructures.Span.t> EGEQ
%token <ProbNv_datastructures.Span.t> EGREATER
%token <ProbNv_datastructures.Span.t> ELESS
%token <ProbNv_datastructures.Span.t> ELEQ
%token <ProbNv_datastructures.Span.t> FGREATER
%token <ProbNv_datastructures.Span.t> FLESS
%token <ProbNv_datastructures.Span.t> FGEQ
%token <ProbNv_datastructures.Span.t> FLEQ
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
%token <ProbNv_datastructures.Span.t> FORWARD
%token <ProbNv_datastructures.Span.t> ASSERT
%token <ProbNv_datastructures.Span.t> TYPE
%token <ProbNv_datastructures.Span.t> COLON
%token <ProbNv_datastructures.Span.t> TBOOL
%token <ProbNv_datastructures.Span.t> TNODE
%token <ProbNv_datastructures.Span.t> TEDGE
%token <ProbNv_datastructures.Span.t * int> TINT
%token <ProbNv_datastructures.Span.t> TFLOAT
%token <ProbNv_datastructures.Span.t> TDICT
%token <ProbNv_datastructures.Span.t> TSET
%token <ProbNv_datastructures.Span.t> EDGES
%token <ProbNv_datastructures.Span.t> NODES
%token <ProbNv_datastructures.Span.t> SYMBOLIC
%token <ProbNv_datastructures.Span.t> MINUS
%token <ProbNv_datastructures.Span.t> SYMB
%token <ProbNv_datastructures.Span.t> MULTI
%token <ProbNv_datastructures.Span.t> CONCRETE
%token <ProbNv_datastructures.Span.t> CREATEMAP
%token <ProbNv_datastructures.Span.t> COMBINE
%token <ProbNv_datastructures.Span.t> SIZE

%token EOF

%start prog
%type  <Syntax.declarations> prog

%start expreof
%type <Syntax.exp> expreof

%right ELSE IN     /* lowest precedence */
%right ARROW
%left AND OR
%nonassoc GEQ GREATER LEQ LESS EQ NLEQ NGEQ NLESS NGREATER ELESS ELEQ EGEQ EGREATER FLEQ FLESS FGEQ
%left PLUS UAND FPLUS
%left FMUL FDIV
%right NOT
%right SOME
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
   | TFLOAT                             { TFloat }
   | LPAREN bty RPAREN                  { $2 }
   | LPAREN tys RPAREN                  { if List.length $2 = 1 then failwith "impossible" else TTuple $2 }
   | TOPTION LBRACKET ty RBRACKET       { TOption $3 }
   | TDICT LBRACKET ty COMMA ty RBRACKET{ TMap ($3,$5) }
   | TSET LBRACKET ty RBRACKET          { TMap ($3,{typ = TBool; mode = Some Concrete}) }
   | LBRACE record_entry_tys RBRACE     { TRecord (make_record_map $2) }
   | ID                                 { (get_user_type (snd $1)).typ }
;

ty:
  | ty ARROW ty                       { {typ=TArrow ($1,$3); mode= Some Concrete} }
  | LPAREN ty RPAREN                  { $2 }  
  | LBRACKET mode RBRACKET bty        { {typ=$4; mode= Some $2} }
  | bty                               { {typ=$1; mode= Some Concrete} }

tys:
  | ty COMMA ty                          { [$1; $3] }
  | ty COMMA tys                         { $1::$3 }
;

record_entry_ty:
  | ID COLON ty                         { snd $1, $3 }
;

record_entry_tys:
  | record_entry_ty                       { [$1] }
  | record_entry_ty SEMI                  { [$1] }
  | record_entry_ty SEMI record_entry_tys { $1::$3 }

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

distPattern:
    | UNDERSCORE                          { DistrPWild }                     
    | LBRACKET INT COMMA INT RBRACKET     { DistrPRange (snd $2,snd $4) }
    | NODE                                { DistrPNode (snd $1)}
    | edgenode TILDE edgenode             { DistrPEdge ($1, $3) }
    | FALSE                               { DistrPBool false }
    | TRUE                                { DistrPBool true }
    /* | LPAREN distPatterns RPAREN          { distr_tuple_pattern $2} */
;

/* distPatterns:
    | distPattern                         { [$1] }
    | distPattern COMMA distPatterns      { $1 :: $3 }
; */

distBranch:
    | BAR distPattern ARROW FLOAT          { ($2, snd $4) }

distBranches:
    | distBranch                          { [$1] }
    | distBranch distBranches             { $1 :: $2 }


assertion:
| expr BAR expr             { ($1, Some $3)}
| expr                      { ($1, None)}

component:
    | SOLUTION ID COMMA ID EQ LPAREN expr COMMA expr COMMA expr COMMA expr RPAREN     { make_dsolve (snd $2) (snd $4) $7 $9 $11 $13}
    | FORWARD LPAREN ID COMMA ID RPAREN EQ LPAREN expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr RPAREN     { make_dfwd (evar (snd $3)) (evar (snd $5)) $9 $11 $13 $15 $17 $19 $21 $23 }
    | LET letvars EQ expr                      { global_let [] $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | options LET letvars EQ expr              { global_let $1 $3 $5 $5.espan (Span.extend $2 $5.espan) }
    | SYMBOLIC ids COLON bty                    { DSymbolic (snd $2, liftSymbolicTy {typ = $4; mode=Some Symbolic}, Uniform) }
    | SYMBOLIC ids COLON bty EQ distBranches    { DSymbolic (snd $2, liftSymbolicTy {typ = $4; mode=Some Symbolic}, DExpr $6) }
    | SYMBOLIC ids COLON bty EQ expr            { DSymbolic (snd $2, liftSymbolicTy {typ = $4; mode=Some Symbolic}, Expr $6) }
    | ASSERT LPAREN assertion RPAREN      { DInfer ("\"\"", fst $3 , snd $3) }
    | ASSERT LPAREN STRING COMMA assertion RPAREN      { DInfer (snd $3, fst $5, snd $5) }
    | EDGES EQ LBRACE RBRACE        { DEdges [] }
    | EDGES EQ LBRACE edges RBRACE  { DEdges $4 }
    | NODES EQ INT                  { DNodes (ProbNv_datastructures.Integer.to_int (snd $3), []) }
    | NODES EQ LPAREN INT COMMA LBRACE nodes RBRACE RPAREN  { DNodes (ProbNv_datastructures.Integer.to_int (snd $4), $7) }
    | TYPE ID EQ ty                     { (add_user_type (snd $2) $4; DUserTy (snd $2, $4)) }
;

components:
    | component                         { [$1] }
    | component components              { $1 :: $2 }
;

option:
    | AT ID                              { Var.name (snd $2)}
;

options:
    | option                         { [$1] }
    | option options                 { $1 :: $2 }
;

record_entry_expr:
  | ID EQ expr                       { snd $1, $3 }
;

record_entry_exprs:
  | record_entry_expr                         { [$1] }
  | record_entry_expr SEMI                    { [$1] }
  | record_entry_expr SEMI record_entry_exprs { $1::$3 }


expreof:
    expr EOF    { $1 }
;

expr:
    | LET letvars EQ expr IN expr       { let span = (Span.extend $1 $6.espan) in
                                          let (id, e) = local_let $2 $4 $4.espan span in
                                          exp (elet id e $6) span }
    | LET LPAREN patterns RPAREN EQ expr IN expr
                                        { let p = tuple_pattern $3 in
                                          let e = ematch $6 (addBranch p $8 emptyBranch) in
                                          let span = Span.extend $1 $8.espan in
                                          exp e span }
    | IF expr THEN expr ELSE expr       { exp (eif $2 $4 $6) (Span.extend $1 $6.espan) }
    (* TODO: span does not include the branches here *)
    | MATCH expr WITH branches          { exp (ematch $2 $4) (Span.extend $1 $3) }
    | FUN params ARROW expr             { make_fun $2 $4 $4.espan (Span.extend $1 $4.espan) }
    /* | FOLDNODE exprsspace               { exp (eop MFoldNode $2) $1 }
    | FOLDEDGE exprsspace               { exp (eop MFoldEdge $2) $1 } */
    /* | MAP exprsspace                    { exp (eop MMap $2) $1 }
    | MAPIF exprsspace                  { exp (eop MMapFilter $2) $1 }
    | MAPITE exprsspace                 { exp (eop MMapIte $2) $1 } */
    | COMBINE expr3 expr3 expr3         { exp (eop MMerge [$2;$3;$4]) $1 } 
    | SIZE expr3 expr3                    { exp (eop MSize [$2;$3]) $1 }
    | CREATEMAP expr                    { exp (eop MCreate [$2]) $1 }
    | expr LBRACKET expr RBRACKET       { exp (eop MGet [$1;$3]) (Span.extend $1.espan $4) }
    | expr LBRACKET expr COLON EQ expr RBRACKET { exp (eop MSet [$1;$3;$6]) (Span.extend $1.espan $7) }
    | SOME expr                         { exp (esome $2) (Span.extend $1 $2.espan) }
    | NOT expr                          { exp (eop Not [$2]) (Span.extend $1 $2.espan) }
    | expr AND expr                     { exp (eop And [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr OR expr                      { exp (eop Or [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr PLUS expr                    { exp (eop (UAdd (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr FPLUS expr                   { exp (eop FAdd [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr FDIV expr                    { exp (eop FDiv [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr FMUL expr                    { exp (eop FMul [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr UAND expr                    { exp (eop (UAnd (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr EQ expr                      { exp (eop Eq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr LESS expr                    { exp (eop (ULess (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GREATER expr                 { exp (eop (ULess (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr LEQ expr                     { exp (eop (ULeq (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GEQ expr                     { exp (eop (ULeq (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr ELESS expr                   { exp (eop ELess [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NLESS expr                   { exp (eop NLess [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NGREATER expr                { exp (eop NLess [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr EGREATER expr                { exp (eop ELess [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr FLESS expr                   { exp (eop FLess [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr FGREATER expr                { exp (eop FLess [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr FLEQ expr                    { exp (eop FLeq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr FGEQ expr                    { exp (eop FLeq [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr NLEQ expr                    { exp (eop NLeq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr NGEQ expr                    { exp (eop NLeq [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr ELEQ expr                    { exp (eop ELeq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr EGEQ expr                    { exp (eop ELeq [$3;$1]) (Span.extend $1.espan $3.espan) }
    | LPAREN expr COLON ty RPAREN       { exp ~ty:(Some $4) $2 (Span.extend $1 $5) }
    | LPAREN expr RPAREN                { exp $2 (Span.extend $1 $3) }
    | expr DOT ID                       { exp (eproject $1 (Var.name (snd $3))) (Span.extend ($1.espan) (fst $3)) }
    | LBRACE record_entry_exprs RBRACE  { exp (erecord (make_record_map $2)) (Span.extend $1 $3) }
    | LBRACE expr WITH record_entry_exprs RBRACE {
                                          let mk_project v =
                                          exp (eproject $2 (Var.name v)) (Span.extend $1 $3) in
                                          let lst = fill_record $4 mk_project in
                                          exp (erecord (make_record_map lst)) (Span.extend $1 $3)
                                        }
    | LBRACE exprs RBRACE               { make_set $2 (Span.extend $1 $3) }
    | LBRACE RBRACE                     { make_set [] (Span.extend $1 $2) }
    | expr2                             { $1 }
; 
expr2:
    | expr2 expr3                       { exp (eapp $1 $2) (Span.extend $1.espan $2.espan) }
    | expr3                             { $1 }
;

expr3:
    | ipaddr                            { $1 }  
    | ID                                { exp (evar (snd $1)) (fst $1) }
    | ID DOT ID                         { exp (eproject (evar (snd $1)) (Var.name (snd $3))) (Span.extend (fst $1) (fst $3)) }
    (*| NUM                               { to_value (vint (snd $1)) (fst $1) }*)
    | INT                               { to_value (vint (snd $1)) (fst $1) }
    | FLOAT                             { to_value (vfloat (snd $1)) (fst $1)}
    | prefixes                          { $1 }
    | NODE                              { to_value (vnode (snd $1)) (fst $1)}
    | edge_arg TILDE edge_arg           { to_value (make_to_edge (snd $1) (snd $3)) (Span.extend (fst $1) (fst $3))}
    | TRUE                              { to_value (vbool true) $1 }
    | FALSE                             { to_value (vbool false) $1 }
    | NONE                              { to_value (voption None) $1 }
    | LPAREN exprs RPAREN               { tuple_it $2 (Span.extend $1 $3) }
;

ipaddr:
  | IPADDRESS         { to_value (vint (ip_to_dec (snd $1))) (fst $1) }

prefixes:
  | ipaddr SLASH INT                    { let pre = to_value (vint (ProbNv_datastructures.Integer.create ~value:(ProbNv_datastructures.Integer.to_int (snd $3)) ~size:6)) (fst $3) in
                                          etuple [$1; pre]}

edge_arg:
  | INT                                 { (fst $1), to_value (vnode (ProbNv_datastructures.Integer.to_int (snd $1))) (fst $1) }
  | NODE                                { (fst $1), to_value (vnode (snd $1)) (fst $1)}

exprs:
    | expr                              { [$1] }
    | expr COMMA exprs                  { $1 :: $3 }
;

id_rec:
  | ID                                {(fst $1, [snd $1])}
  | ID COMMA id_rec                   {let span = (Span.extend (fst $1) (fst $3)) in (span, (snd $1) :: (snd $3))}

ids:
    | ID                              { (fst $1, [snd $1]) }
    | LPAREN id_rec RPAREN            { $2 }
;

edgenode:
    | INT                               { ProbNv_datastructures.Integer.to_int (snd $1) }
    | NODE                              { snd $1 }
;

edge:
    | edgenode TILDE edgenode SEMI      { [($1, $3, let () = incr edge_id in !edge_id)] }
    | edgenode SUB edgenode SEMI        { [($1, $3, let () = incr edge_id in !edge_id)] }
    | edgenode EQ edgenode SEMI   { [($1, $3, (incr edge_id; !edge_id)); ($3, $1, (incr edge_id; !edge_id))] }
    | LPAREN edgenode TILDE edgenode COMMA INT RPAREN SEMI      { [($2, $4, ProbNv_datastructures.Integer.to_int (snd $6))] }
    | LPAREN edgenode SUB edgenode COMMA INT RPAREN SEMI        { [($2, $4, ProbNv_datastructures.Integer.to_int (snd $6))] }
    | LPAREN edgenode EQ edgenode COMMA INT COMMA INT RPAREN SEMI   { [($2, $4, ProbNv_datastructures.Integer.to_int (snd $6)); ($4, $2, ProbNv_datastructures.Integer.to_int (snd $8))] }
;

edges:
    | edge                              { $1 }
    | edge edges                        { $1 @ $2 }
;

node:
    | NODE COLON STRING               { [(snd $1,snd $3)] }

nodes:
    | node SEMI                         { $1 }
    | node SEMI nodes                   { $1 @ $3}

  pattern:
    | UNDERSCORE                        { PWild }
    | ID                                { PVar (snd $1) }
    | TRUE                              { PBool true }
    | FALSE                             { PBool false }
    | INT                               { PInt (snd $1) }
    | INT DOT INT                       { PFloat (float_of_string @@ Printf.sprintf "%d.%d" (Integer.to_int @@ snd $1) (Integer.to_int @@ snd $3)) }
    | NODE                              { PNode (snd $1) }
    | pattern TILDE pattern             { PEdge (ensure_node_pattern $1, ensure_node_pattern $3)}
    | LPAREN patterns RPAREN            { tuple_pattern $2 }
    | NONE                              { POption None }
    | SOME pattern                      { POption (Some $2) }
    | LBRACE record_entry_ps RBRACE     { PRecord (make_record_map
                                          (if snd $2
                                           then fill_record (fst $2) (fun _ -> PWild)
                                           else fst $2)) }
;

patterns:
    | pattern                           { [$1] }
    | pattern COMMA patterns            { $1::$3 }
;

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

record_entry_p:
  | ID EQ pattern                    { snd $1, $3 }
;

record_entry_ps:
  | record_entry_p                      { ([$1], false) }
  | record_entry_p SEMI                 { ([$1], false) }
  | record_entry_p SEMI UNDERSCORE      { ([$1], true) }
  | record_entry_p SEMI record_entry_ps { ($1::(fst $3), snd $3) }