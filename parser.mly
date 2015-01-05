/* File parser.mly */
%{
(* Open is used for importing another module. 
   Each file is organized as a module with the module name being the
   file name without extension where the first letter is capitalized
*)
open ImpAST  (* refer to definitions from ImpAST directly *)
open Lexing  (* Lexing is a predefined library used for lexing *)

(* Formats a string describing the location of the production being currently 
   parsed *)
let location () =  let start_pos = Parsing.symbol_start_pos () in
    let end_pos = Parsing.symbol_end_pos () in
    (start_pos.pos_fname,start_pos.pos_lnum, start_pos.pos_cnum - start_pos.pos_bol, end_pos.pos_lnum, end_pos.pos_cnum - end_pos.pos_bol)

(* Throws a ParseError with the specified location*)
let parseError loc = raise (Lexer.ParseError loc)

%}
/* Token symbol declarations.  Tokens represent terminals/literals in the
   grammar defined below. Each token must be declared here. */
%token INT_CAST FLOAT_CAST  /* we can declare multiple tokens per line */
/* tokens can be parameterized by types which will be their value */
%token <int> INT
%token <float> FLOAT
%token <string> VAR
%token TRUE FALSE
%token SEQ SKIP
%token IF THEN ELSE
%token WHILE DO DONE
%token FOR
%token LT LTE EQ
%token ASGNOP DEREF
%token PLUS MINUS MUL DIV
%token LPAREN RPAREN
%token FUN COLON
%token LET REC IN
%token REF
%token TINT TBOOL TUNIT TFLOAT
%token ARROW
%token MATCH WITH INJL INJR PIPE
%token EOF
/* Precedence list.  One can think of it like this:  
   Reject a parse tree if two symbols in the list below occur one next to 
   the other in a parse tree but their order is reversed from the order below.
   Example:  
     3 + 5 * 7 can be parsed as either 
         +                     or                     *
        / \                                          / \
       3   *                                        +   7
          / \                                      / \
         5   7                                    3   5
    However, the second tree does not respect the precedence, as
    MUL is direcly above PLUS in the tree, while in the precedence list it is
    below PLUS.
*/
%nonassoc FUNX /* lowest precedence */
%right ARROW
%right SEQ
/* Grouping constraints: left/right/nonassoc say how multiple consecutive 
   occurrences of operators with the same precedence should be grouped.
   %right:  reject a parse tree if two symbols in the list below occur one next 
   the other in a parse tree but the one below is not at the right 
   of the one on top.
   Example:  
     x := 3 ; () ; x := 7 can be parsed as either 
         ;                     or                     ;
        / \                                          / \
      x:=  ;                                        ;  x:=
       |  / \                                      / \  |
       3 () x:=                                  x:= () 7
             |                                    |
             7                                    3
    However, the second tree does not respect the %right declaration for SEQ, as
    SEQ is direcly below on the left side of  SEQ in the tree.
 
   Same holds true for multiple tokens at the same level. For example,
     3 - 5 + 7 can be parsed as either 
         -                     or                     +
        / \                                          / \
       3   +                                        -   7
          / \                                      / \
         5   7                                    3   5
 
    However, the first tree does not respect the %left declaration 
    for PLUS and MINUS, as PLUS is direcly below on the right side of MINUS
    in the tree.
*/
%nonassoc FORX  /* added to resolve precedence problems for for body */
%nonassoc IFX /* added to resolve precedence problems for else branch */
%nonassoc LT LTE EQ
%right ASGNOP
%left PLUS MINUS
%left MUL DIV
%nonassoc INT_CAST FLOAT_CAST
%left APPX
%nonassoc DEREF REF      /* highest precedence */
%start main             /* the entry point/start symbol */
%type <ImpAST.expr> main  /* the datatype associated to the start symbol */
%%

/* production for the start symbol.  we have one expression followed by EOF */
main:
    expr EOF                { $1 }
/* for each case, the left side specifiess the grammar production, while the
   right side (between curly brackets) specifies what how the 
   result associated to the production is formed.  for us it will be a value
   of the expr type defined in impast.ml 
*/
;

/* grammar productions for expression types */
tip:
  | TINT                       {TInt}
  | TBOOL                      {TBool}
  | TUNIT                      {TUnit}
  | TFLOAT                     {TFloat}
  | tip ARROW tip              { TArrow ($1, $3) }
  /* the TArrow type constructor is used to represent 
    functional types of the form a -> b */
  /* the $n variables are used to get the value corresponding to the nth
     element of the production (counting from 1) */
  | LPAREN tip RPAREN          { $2 }
  | tip REF                    { TRef $1 }  /* reference type */
  | tip PLUS tip              { TSum ($1, $3) }

expr:
  | expr PLUS expr             { Op ($1,Plus,$3, location()) }
  /*  We add location information to all expression constructs to allow for
      localized error messages */
  | expr MINUS expr             { Op ($1,Minus,$3, location()) }
  | expr MUL expr             { Op ($1,Mul,$3, location()) }
  | expr DIV expr             { Op ($1,Div,$3, location()) }
  | expr ASGNOP expr            { Atrib ($1,$3, location()) }
  | expr LTE expr              { Op ($1, Mic, $3, location()) }
  | expr LT expr              { Op ($1, MicS, $3, location()) }
  | expr SEQ expr              { Secv ($1,$3, location()) }
  | IF expr THEN expr ELSE expr %prec IFX
                               { If ($2, $4, $6, location()) }
  /* %prec IFX specifies that the expression on the IFX branch should have 
     precedence at least IFX.  It will reject therefore parse trees in which
     the symbol at the top of the expression on the else branch is higher than
     IFX in the precedence list.   Example:
     if true then () else () ; x := 3  can be parsed as either 
          If                    or                      ;
        / | \                                         /   \
     true () ;                                       If   x:=
            / \                                     / | \  | 
           () x:=                               true () () 3
               |                                    
               3                                   
    However, the first tree does not respect the %prec IFX declaration for else
    as SEQ is direcly below if on the else branch, while in the precedence list
    SEQ is above IFX.
  */
 
  | WHILE expr DO expr DONE    { While ($2, $4, location()) }
  | FOR LPAREN expr SEQ expr SEQ expr RPAREN expr %prec FORX
                               { For ($3, $5, $7, $9, location()) }
  | FUN LPAREN VAR COLON tip RPAREN ARROW expr %prec FUNX
                               { Fun ($3, $5, $8, location()) }
  | LET REC VAR COLON tip EQ expr IN expr %prec FUNX
                               { LetRec ($3, $5, $7, $9, location()) }
  | LET VAR EQ expr IN expr %prec FUNX
                               { Let ($2, $4, $6, location()) }
  | expr funexpr               { App ($1, $2, location()) }
  /* sometimes precedences are not enough so we must resort 
     to multiple non-terminals. Here we say that only certain expressions
     defined by funexpr can be arguments to function application.   */
  | funexpr                    { $1 }
  /* here we say that those expressions defined by funexps 
     are themselves expr */
  | INJL funexpr COLON tip     { InjL($2, $4, location()) }
  | INJR funexpr COLON tip     { InjR($2, $4, location()) }
  | MATCH expr WITH 
       INJL LPAREN VAR COLON tip RPAREN ARROW expr PIPE 
       INJR LPAREN VAR COLON tip RPAREN ARROW expr
                               { Match($2, Fun($6, $8, $11, location()),
                                           Fun($15, $17, $20, location()), 
                                           location()) }
  /* For simplicity, the cases of match are encoded as function declarations */
  | error                      { parseError (location ()) }
;

funexpr:
  | INT                        { Int ($1,location()) }
  | FLOAT                      { Float ($1,location()) }
  | TRUE                       { Bool (true, location()) }
  | FALSE                      { Bool (false, location()) }
  | SKIP                       { Skip (location()) }
  | VAR                        { Var ($1,location()) }
  | INT_CAST                   { IntOfFloat (location()) }
  | FLOAT_CAST                 { FloatOfInt (location()) }
  | LPAREN expr RPAREN         { $2 }
  /* having expression between parens here says that one can have any
     expression as argument to a function application if the expression
     is wrapped in parentheses */
  | DEREF expr                 { Deref ($2, location()) }
  | REF expr                   { Ref ($2, location()) }
;
