open Lexing
open Types
open ImpAST

let type_and_run debug pgm =
      if (type_check pgm) then begin
          Printf.printf "The program typechecks. Executing..." ;
          if debug then print_newline () else () ;
          flush stdout ;
          let final = (Semantics.evaluate debug (pgm,[])) in
            Printf.printf " done.\n Final configuration:\n\n  %s\n\n"
                  (Semantics.string_of_config final)
      end else ()


let cin () =
      if Array.length Sys.argv > 1
      then open_in Sys.argv.(1)
      else failwith "please specify program file"

let _ =
  let lexbuf = Lexing.from_channel (cin ()) in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = Sys.argv.(1) };
    try
      let pgm = Parser.main Lexer.token lexbuf in
       type_and_run (Array.length Sys.argv > 2) pgm
    with
      Lexer.LexerError loc ->
        Printf.eprintf "Lexer Error: Unexpected token '%s' at %s\n" (Lexing.lexeme lexbuf) loc
    | Lexer.ParseError loc ->
        Printf.eprintf "Parse Error: Unexpected token '%s' at %s\n" (Lexing.lexeme lexbuf) loc
