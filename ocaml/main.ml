
open Lexer
open Parser
open Parser_pp
open Pervasives

open Datatypes
open Specif

open Defns
open Refin

let filename = Sys.argv.(1)
let term = (Termstar_nl_pi_intro (Typestar_nl_mtvar 0 , Termstar_nl_mvar 1))

let pp_goal g t =
    match g with
    | Coq_inleft (foo, _) -> "The goal for term >>" ^ Parser_pp.pp_ete t ^
        "<< is: " ^ "\n\n\t" ^  Parser_pp.pp_tTGoal foo 
    | Coq_inright -> "The term >>" ^ Parser_pp.pp_ete t ^ "<< cannot be refined"

let pp_prog p =
    match p with
    | Coq_inleft (foo, _) -> "The program is: " ^ "\n\n\t" ^ 
        Parser_pp.pp_tTProg foo 
    | Coq_inright -> "The signature cannot be refined"

let parseVal fn
    (vp : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a) =
    let inBuffer = open_in fn in
    let lineBuffer = Lexing.from_channel inBuffer in 
    try
        vp (Lexer.token) (lineBuffer)
    with
        | Lexer.Error msg -> raise (Failure (Printf.sprintf "%s: %s%!\n" fn msg))
        | Parser.Error -> raise (Failure (Printf.sprintf "%s, at offset %d: syntax error.\n%!"
            fn (Lexing.lexeme_start lineBuffer))) 
        
;;

  

let () =
        let sigma = parseVal (Sys.argv.(1)) (Parser.esgn_start) in 
        let t = parseVal (Sys.argv.(2)) (Parser.ete_start) in 
        let g = Refin.goalterm_dec sigma [] t 0 in
        let p = Refin.progsig_dec sigma 0 in
            print_string (Parser_pp.pp_esgn sigma);
            print_newline(); 
            print_string (pp_prog p);
            print_newline(); 
            print_string (pp_goal g t);
            print_newline();
            print_newline()
    ;;
