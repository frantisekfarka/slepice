open Lexer
open Parser
open Parser_pp
open Pervasives

let filename = Sys.argv.(1)


let () =
    let inBuffer = open_in filename in
    let lineBuffer = Lexing.from_channel inBuffer in 
    try
        let ix = Parser.ix_start Lexer.token lineBuffer in
            print_string (Parser_pp.pp_ix ix); print_newline(); 
    with
        | Lexer.Error msg -> Printf.fprintf stderr "%s%!\n" msg
        | Parser.Error -> Printf.fprintf stderr "At offset %d: syntax error.\n%!" (Lexing.lexeme_start lineBuffer)


