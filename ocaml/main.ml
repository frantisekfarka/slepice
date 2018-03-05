
open Lexer
open Parser
open Parser_pp
open Pervasives

open Datatypes
open Specif

open Defns
open Refin

let filename = Sys.argv.(1)
let term = (Termstar_nl_pi_intro (Typestar_nl_mtvar 0 , Termstar_nl_mvar 0))

let pp_goal g t =
    match g with
    | Coq_inleft (foo, _) -> "The goal for term >>" ^ Parser_pp.pp_ete t ^
        "<< is: " ^ Parser_pp.pp_tTGoal foo 
    | Coq_inright -> "The term >>" ^ Parser_pp.pp_ete t ^ "<< cannot be refined"
    ;;

let () =
    let inBuffer = open_in filename in
    let lineBuffer = Lexing.from_channel inBuffer in 
    try
        let sigma = Parser.esgn_start Lexer.token lineBuffer in
        let g1 = Refin.goalterm_dec 
                sigma
                []
                term
                0 in
            print_string (Parser_pp.pp_esgn sigma);
            print_newline(); 
        
            print_string (pp_goal g1 term);
            print_newline(); 
    with
        | Lexer.Error msg -> Printf.fprintf stderr "%s%!\n" msg
        | Parser.Error -> Printf.fprintf stderr "At offset %d: syntax error.\n%!" (Lexing.lexeme_start lineBuffer)


