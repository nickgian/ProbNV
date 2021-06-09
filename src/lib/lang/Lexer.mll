
{
  open Batteries
  open Parser
  open Printf
  open ProbNv_datastructures.Span
  exception Eof

  let position lexbuf =
    {fname=(lexbuf.Lexing.lex_start_p).pos_fname; start=Lexing.lexeme_start lexbuf; finish=Lexing.lexeme_end lexbuf}

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <-
      { pos with Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
                 Lexing.pos_bol = pos.Lexing.pos_cnum; } ;;

}

let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']*
let symbol = ['~' '`' '!' '@' '#' '$' '%' '^' '&' '|' ':' '?' '>' '<' '[' ']' '=' '-' '.' '_' '(' ')']+
let num = ['0'-'9']+
let float = ['0'-'9']+['.']+['0'-'9']+
let prob_literal = (['0']['.']['0'-'9']+)"p" | ("1.0p")
let width = "u"num
let tid = ['\'']['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*
let node = num"n"
let wspace = [' ' '\t']
let filename = "\""(['a'-'z' 'A'-'Z' '0'-'9' '_' '\\' '/' '.' '-'])+"\""
let string = "\""([^'\"'])*"\""

rule token = parse
  | "include" wspace* filename {token lexbuf} (* Include directives are processed separately *)
  | "(*"              { comments 0 lexbuf }
  | "false"           { FALSE (position lexbuf) }
  | "true"            { TRUE (position lexbuf) }
  | "let"             { LET (position lexbuf) }
  | "@noinline"       { NOINLINE (position lexbuf) }
  | "in"              { IN (position lexbuf) }
  | "if"              { IF (position lexbuf) }
  | "then"            { THEN (position lexbuf) }
  | "else"            { ELSE (position lexbuf) }
  | "fun"             { FUN (position lexbuf) }
  | "symbolic"        { SYMBOLIC (position lexbuf) }
  | "None"            { NONE (position lexbuf) }
  | "Some"            { SOME (position lexbuf) }
  | "edges"           { EDGES (position lexbuf) }
  | "nodes"           { NODES (position lexbuf) }
  | "match"           { MATCH (position lexbuf) }
  | "with"            { WITH (position lexbuf) }
  | "createDict"      { CREATEMAP (position lexbuf) }
  | "combine"         { COMBINE (position lexbuf) }
  | "size"            { SIZE (position lexbuf) }
  (* | "union"           { UNION (position lexbuf) }
  | "inter"           { INTER (position lexbuf) } *)
  | "set"             { TSET (position lexbuf) }
  | "dict"            { TDICT (position lexbuf) }
  | "option"          { TOPTION (position lexbuf) } 
  | "int" num as s    { TINT (position lexbuf, int_of_string @@ String.lchop ~n:3 s) }
  | "int"             { TINT (position lexbuf, 32) }
  | "bool"            { TBOOL (position lexbuf) }
  | "tnode"           { TNODE (position lexbuf) }
  | "tedge"           { TEDGE (position lexbuf) }
  | "float"           { TFLOAT (position lexbuf) }
  | "type"            { TYPE (position lexbuf) }
  | "solution"        { SOLUTION (position lexbuf) }
  | "forward"         { FORWARD (position lexbuf) }
  | "assert"          { ASSERT (position lexbuf) }
  | "S"               { SYMB (position lexbuf)}
  | "M"               { MULTI (position lexbuf)}
  | "C"               { CONCRETE (position lexbuf)}
  | id as s           { ID (position lexbuf, ProbNv_datastructures.Var.create s) }
  | node as s         { NODE (position lexbuf, int_of_string (String.rchop ~n:1 s)) }
  | num width as n    { NUM (position lexbuf, ProbNv_datastructures.Integer.of_string n) }
  | num as n          { INT (position lexbuf, ProbNv_datastructures.Integer.of_string n) }
  | prob_literal as n { PROB (position lexbuf, float_of_string (String.rchop ~n:1 n))}
  | string as s       { STRING (position lexbuf, s)}
  | "&&"              { AND (position lexbuf) }
  | "||"              { OR (position lexbuf) }
  | "|"               { BAR (position lexbuf) }
  | "->"              { ARROW (position lexbuf) }
  | "!"               { NOT (position lexbuf) }
  | ","               { COMMA (position lexbuf) }
  | "~"               { TILDE (position lexbuf) }
  | "+" width as s    { PLUS (position lexbuf, int_of_string @@ String.lchop ~n:2 s) }
  | "+"               { PLUS (position lexbuf, 32) }
  | "+."              { FPLUS (position lexbuf) }
  | "/."              { FDIV (position lexbuf) }
  | "-" width as s    { SUB (position lexbuf, int_of_string @@ String.lchop ~n:2 s) }
  | "-"               { SUB (position lexbuf, 32) }
  | "&" width as s    { UAND (position lexbuf, int_of_string @@ String.lchop ~n:2 s) }
  | "&"               { UAND (position lexbuf, 32) }
  | "<=n"             { NLEQ (position lexbuf) }
  | "<=e"             { ELEQ (position lexbuf) }
  | "<=" width as s   { LEQ (position lexbuf, int_of_string @@ String.lchop ~n:3 s) }
  | "<="              { LEQ (position lexbuf, 32) }
  | ">=n"             { NGEQ (position lexbuf) }
  | ">=e"             { EGEQ (position lexbuf) }
  | ">=" width as s   { GEQ (position lexbuf, int_of_string @@ String.lchop ~n:3 s) }
  | ">="              { GEQ (position lexbuf, 32) }
  | "="               { EQ (position lexbuf) }
  | "<n"              { NLESS (position lexbuf) }
  | "<e"              { ELESS (position lexbuf) }
  | "<" width as s    { LESS (position lexbuf, int_of_string @@ String.lchop ~n:2 s) }
  | "<"               { LESS (position lexbuf, 32) }
  | "<."              { FLESS (position lexbuf) }
  | ">."              { FGREATER (position lexbuf) }
  | "<=."              { FLEQ (position lexbuf) }
  | ">=."              { FGEQ (position lexbuf) }
  | ">n"              { NGREATER (position lexbuf) }
  | ">e"              { EGREATER (position lexbuf) }
  | ">" width as s    { GREATER (position lexbuf, int_of_string @@ String.lchop ~n:2 s) }
  | ">"               { GREATER (position lexbuf, 32) }
  | ";"               { SEMI (position lexbuf) }
  | ":"               { COLON (position lexbuf) }
  | "("               { LPAREN (position lexbuf) }
  | ")"               { RPAREN (position lexbuf) }
  | "["               { LBRACKET (position lexbuf) }
  | "]"               { RBRACKET (position lexbuf) }
  | "{"               { LBRACE (position lexbuf) }
  | "}"               { RBRACE (position lexbuf) }
  | "_"               { UNDERSCORE (position lexbuf) }
  | "."               { DOT (position lexbuf) }
  | "/"               { SLASH (position lexbuf) }
  | wspace            { token lexbuf }
  | '\n'              { incr_linenum lexbuf; token lexbuf}
  | _ as c            { printf "[Parse Error] Unrecognized character: %c\n" c; token lexbuf }
  | eof		            { EOF }

and comments level = parse
  | "*)"  { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "(*"  { comments (level+1) lexbuf }
  | '\n'  { incr_linenum lexbuf; comments level lexbuf}
  | _     { comments level lexbuf }
  | eof   { raise End_of_file }
