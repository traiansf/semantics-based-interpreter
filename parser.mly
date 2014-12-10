/* File parser.mly */
%{
open ImpAST
open Lexing

let location () =  let start_pos = Parsing.symbol_start_pos () in
    let end_pos = Parsing.symbol_end_pos () in
    Printf.sprintf "%s:%d.%d-%d.%d"
      start_pos.pos_fname
      start_pos.pos_lnum (start_pos.pos_cnum - start_pos.pos_bol)
      end_pos.pos_lnum (end_pos.pos_cnum - end_pos.pos_bol)

let parseError loc = raise (Lexer.ParseError loc)

%}
%token Z
%token INT_CAST FLOAT_CAST
%token <int> INT
%token <float> FLOAT
%token <string> LOC
%token <string> VAR
%token WILD
%token TRUE FALSE
%token SEQ SKIP
%token COMMA
%token MATCH WITH CHOICE
%token IF THEN ELSE
%token WHILE DO DONE
%token FOR
%token LT LTE EQ
%token ASGNOP DEREF
%token PLUS MINUS MUL DIV
%token LPAREN RPAREN
%token FUN COLON FUNCTION
%token LET REC IN
%token REF
%token TINT TBOOL TUNIT TFLOAT
%token ARROW FUNX
%token EOF
%left CHOICE /* lowest precedence */
%nonassoc FUNX
%right ARROW
%right SEQ
%nonassoc FORX
%nonassoc IFX
%nonassoc LT LTE EQ
%right ASGNOP
%left PLUS MINUS
%left MUL DIV
%nonassoc INT_CAST FLOAT_CAST
%left APPX
%nonassoc DEREF REF      /* highest precedence */
%start main             /* the entry point */
%type <ImpAST.expr> main
%%
main:
    expr EOF                { $1 }
;

tip:
  | basetip MUL prodtip       { TProd($1::$3) }
  | basetip                   { $1 }
;

prodtip:
  | basetip MUL prodtip        { $1::$3 }
  | basetip                    { [$1] }           
;

basetip:
  | TINT                       {TInt}
  | TBOOL                      {TBool}
  | TUNIT                      {TUnit}
  | TFLOAT                     {TFloat}
  | tip ARROW tip              { TArrow ($1, $3) }
  | LPAREN tip RPAREN          { $2 }
  | tip REF                    { TRef $1 }
;

expr: 
  | baseexpr COMMA exprtuple { Tuple($1::$3, location()) }
  | baseexpr                 { $1 }
;

exprtuple:
  | baseexpr COMMA exprtuple { $1::$3 }
  | baseexpr                 { [$1] }
;

baseexpr:
  | expr PLUS expr             { Op ($1,Plus,$3, location()) }
  | expr MINUS expr             { Op ($1,Minus,$3, location()) }
  | expr MUL expr             { Op ($1,Mul,$3, location()) }
  | expr DIV expr             { Op ($1,Div,$3, location()) }
  | expr ASGNOP expr            { Atrib ($1,$3, location()) }
  | expr LTE expr              { Op ($1, Mic, $3, location()) }
  | expr LT expr              { Op ($1, MicS, $3, location()) }
  | expr SEQ expr              { Secv ($1,$3, location()) }
  | IF expr THEN expr ELSE expr %prec IFX
                               { If ($2, $4, $6, location()) }
  | WHILE expr DO expr DONE    { While ($2, $4, location()) }
  | FOR LPAREN expr SEQ expr SEQ expr RPAREN expr %prec FORX
                               { For ($3, $5, $7, $9, location()) }
  | FUN choice                 { Fun ($2, location()) }
  | FUNCTION choices           { Function ($2, location()) }
  | LET REC VAR COLON tip EQ expr IN expr %prec FUNX
                               { LetRec ($3, $5, $7, $9, location()) }
  | LET expr EQ expr IN expr %prec FUNX
                               { Let ($2, $4, $6, location()) }
  | MATCH expr WITH choices    { Match ($2, $4, location()) }
  | expr funexpr               { App ($1, $2, location()) }
  | funexpr                    { $1 }
  | error                      { parseError (location ()) }
;

choices:
  | choice CHOICE choices      { $1::$3 }
  | choice                     { [$1] }
;

choice:
  expr ARROW expr %prec FUNX  { Case($1, $3, location()) }
;

funexpr:
  | INT                        { Int ($1,location()) }
  | FLOAT                      { Float ($1,location()) }
  | TRUE                       { Bool (true, location()) }
  | FALSE                      { Bool (false, location()) }
  | SKIP                       { Skip (location()) }
  | VAR                        { Var ($1,location()) }
  | WILD                       { AnyVar (location()) }
  | INT_CAST                   { IntOfFloat (location()) }
  | FLOAT_CAST                 { FloatOfInt (location()) }
  | Z                          { Z (location()) }
  | LPAREN expr RPAREN         { $2 }
  | DEREF expr                 { Deref ($2, location()) }
  | REF expr                   { Ref ($2, location()) }
  | typedexpr                  { $1 }
;

typedexpr:
  | LPAREN expr COLON tip RPAREN { TypedExpr($2, $4, location()) }
