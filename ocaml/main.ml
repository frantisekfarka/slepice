
open Lexer
open Parser
open Parser_pp
open Pervasives

open Datatypes
open Specif

open Defns
open Refin

open Helpers

let read_signature_filename_opt = ref (None : string option)
let read_term_filename_opt = ref (None : string option)
let write_basename_opt = ref (None : string option)
let print_sig = ref false
let print_term = ref false

let options = Arg.align [
    ( "-sig", 
      Arg.String (fun s -> 
        match !read_signature_filename_opt with
        | None -> read_signature_filename_opt  := Some s
        | Some _ -> Helpers.error "\nError: multiple -sig <filename> not suppported\n"),
        "<filename>        Input signature" );
    ( "-term", 
      Arg.String (fun s -> 
        match !read_term_filename_opt with
        | None -> read_term_filename_opt  := Some s
        | Some _ -> Helpers.error "\nError: multiple -term <filename> not suppported\n"),
        "<filename>        Input term" );
    ( "-o", 
      Arg.String (fun s -> 
        match !write_basename_opt with
        | None -> write_basename_opt  := Some s
        | Some _ -> Helpers.error "\nError: multiple -o <filename> not suppported\n"),
        "<basename>        Output files basename" );
  ( "-print-sig",
    Arg.Bool (fun b -> print_sig := b),
    "<"^string_of_bool !print_sig^">  Print parsed signature" );
  ( "-print-term",
    Arg.Bool (fun b -> print_term := b),
    "<"^string_of_bool !print_sig^">  Print parsed term" );
  ( "-print",
    Arg.Bool (fun b -> print_sig := b; print_term := b),
    "<"^string_of_bool (!print_sig && !print_term) ^">  Print parsed signature and term" );
]

let usage_msg =
    ("\n"
     ^ "usage: slepice <options> -sig <filename> -term <filename> [ -o <basename> ]\n"
    )




let pp_goal g =
    match g with
    | Coq_inleft (foo, _) -> Parser_pp.pp_tTGoal foo 
    | Coq_inright -> error "The term cannot be refined"

let pp_prog p =
    match p with
    | Coq_inleft (foo, _) -> Parser_pp.pp_tTProg foo 
    | Coq_inright -> error "The signature cannot be refined"

let parseVal fn
    (vp : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a) =
    let inBuffer = open_in fn in
    let lineBuffer = Lexing.from_channel inBuffer in 
    try
        vp (Lexer.token) (lineBuffer)
    with
        | Lexer.Error msg -> error (Printf.sprintf "in %s, %s%!\n" fn msg)
        | Parser.Error -> error (Printf.sprintf "in %s, at offset %d: syntax error.\n%!"
            fn (Lexing.lexeme_start lineBuffer)) 
        
;;


let _ =
    let arguments = ref [] in
      Arg.parse options
        (fun s -> arguments := s :: !arguments)
        usage_msg
;;


let input_signature_opt = 
    Datatypes.option_map
        (fun fn -> parseVal fn Parser.esgn_start)
        !read_signature_filename_opt
  
let input_term_opt = 
    Datatypes.option_map
        (fun fn -> parseVal fn Parser.ete_start)
        !read_term_filename_opt

let output_prog_ch =
  match !write_basename_opt with
    | Some bn -> open_out (bn ^ ".prog") 
    | None -> stdout
  
let output_goal_ch =
  match !write_basename_opt with
    | Some bn -> open_out (bn ^ ".g") 
    | None -> stdout

let process_print_sig s =
    if !print_sig then
        Printf.printf "\n---\nParsed signature:\n%s\n\n---\n\n" (Parser_pp.pp_esgn s)
    else ()

let process_print_term t =
    if !print_term then
        Printf.printf "\n---\nParsed term:\n%s\n\n---\n\n" (Parser_pp.pp_ete t)
    else ()

let () =
    match input_signature_opt , input_term_opt with
      | None, _ -> error "No input signature provided .."
      | _, None -> error "No input term provided .."
      | (Some s , Some t) -> 
            let g = Refin.goalterm_dec s [] t 0 in
            let p = Refin.progsig_dec s 0 in
                process_print_sig s;
                process_print_term t;
                Printf.fprintf output_prog_ch "%s\n" (pp_prog p);
                Printf.fprintf output_goal_ch "%s\n" (pp_goal g);


