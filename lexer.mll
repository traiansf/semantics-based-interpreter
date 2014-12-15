(* File lexer.mll *)
{
open Parser        (* The type token is defined in parser.mli *)

exception LexerError of string
exception ParseError of string

(*  Code for maintaining line numbers while tokenizing *)

let incr_linenum lexbuf =
      let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with
        (* incrementing line number *)
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        (* setting offset for beggining of line *)
        Lexing.pos_bol = pos.Lexing.pos_cnum;
      }

let lex_error lexbuf =
         begin
           let curr = lexbuf.Lexing.lex_curr_p in
           let file = curr.Lexing.pos_fname
           and line = curr.Lexing.pos_lnum
           and cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
              raise (LexerError (Printf.sprintf "%s:%d.%d" file line cnum))
         end

let keyword_table = Hashtbl.create 20
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
  [
   ( "fun"          , FUN );
   ( "function"     , FUNCTION );
   ( "int"          , TINT );
   ( "bool"         , TBOOL );
   ( "float"        , TFLOAT );
   ( "string"       , TSTRING );
   ( "unit"         , TUNIT );
   ( "int_of_float" , INT_CAST );
   ( "float_of_int" , FLOAT_CAST );
   ( "if"           , IF );
   ( "then"         , THEN );
   ( "else"         , ELSE );
   ( "while"        , WHILE );
   ( "do"           , DO );
   ( "done"         , DONE );
   ( "for"          , FOR );
   ( "true"         , TRUE );
   ( "false"        , FALSE );
   ( "let"          , LET );
   ( "rec"          , REC );
   ( "in"           , IN );
   ( "ref"          , REF );
   ( "match"        , MATCH );
   ( "with"         , WITH );
   ( "type"         , TYPE );
   ( "of"           , OF );
]

}

rule token = parse
    [ '\n' ] { incr_linenum lexbuf ; token lexbuf } (* count lines *)
 | "(*"            { comments 0 lexbuf }
                                    (* skip line comments but count lines *)
  | [' ' '\t' '\r' ]     { token lexbuf }     (* skip blanks *)
  | ['-']?['0'-'9']+['.']['0'-'9']* as lxm { FLOAT(float_of_string lxm) }
  | ['-']?['0'-'9']+ as lxm { INT(int_of_string lxm) }
  | '"' { let buffer = Buffer.create 20 in
          STRING (stringl buffer lexbuf) }
  | "->"           { ARROW }
  | '+'            { PLUS }
  | '-'            { MINUS }
  | '*'            { MUL }
  | '/'            { DIV }
  | '<'            { LT }
  | "<="           { LTE }
  | "()"           { SKIP }  
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | "="            { EQ }
  | ":="           { ASGNOP }
  | ":"            { COLON }
  | ';'            { SEQ }
  | ";;"           { DOUBLESEQ }
  | ','            { COMMA }
  | '|'            { CHOICE }
  | '_'            { WILD }
 | '!'            { DEREF }
  | ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_'] * as variant   { VARIANT(variant) }
  | ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\''] * as id
                   { try Hashtbl.find keyword_table id 
                     with Not_found -> ID(id) }
  | eof            { EOF }
  | _              { lex_error lexbuf }
and comments level = parse
  | "*)"        { if level = 0 then token lexbuf
                  else comments (level-1) lexbuf }
  | "(*"        { comments (level+1) lexbuf }
  | [ '\n' ]    { incr_linenum lexbuf ; comments level lexbuf } (* count lines *)
  | _           { comments level lexbuf }
  | eof         { raise End_of_file }
 and  stringl buffer = parse
 | '"' { Buffer.contents buffer }
 | "\\t" { Buffer.add_char buffer '\t'; stringl buffer lexbuf }
 | "\\n" { Buffer.add_char buffer '\n'; stringl buffer lexbuf }
 | "\\n" { Buffer.add_char buffer '\n'; stringl buffer lexbuf }
 | '\\' '"' { Buffer.add_char buffer '"'; stringl buffer lexbuf }
 | '\\' '\\' { Buffer.add_char buffer '\\'; stringl buffer lexbuf }
 | eof { raise End_of_file }
 | _ as char { Buffer.add_char buffer char; stringl buffer lexbuf }

