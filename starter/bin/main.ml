open Imp

let usage = 
  "dune exec imp parse [opts] e:  parse e\n" ^
  "dune exec imp exec p:  execute program p (path to file)\n"

let arg : string option ref = ref None

type cmd_t = Cmd_parse | Cmd_exec

let cmd : cmd_t option ref = ref None

let cmd_opts : (Arg.key*Arg.spec*Arg.doc) list ref = ref []

type parse_cmd_t = Expr | Stm | Pgm | PgmFile
let parse_cmd : parse_cmd_t ref = ref PgmFile
let parse_cmd_opts = [
    ("--expr", Arg.Unit (fun () -> parse_cmd := Expr), 
        "Parse argument as expression.");
    ("--stm", Arg.Unit (fun () -> parse_cmd := Stm),
        "Parse argument as statement.");
    ("--pgm", Arg.Unit (fun () -> parse_cmd := Pgm),
        "Parse argument as program");
    ("--pgmfile", Arg.Unit (fun () -> parse_cmd := PgmFile),
        "Parse program in file (default)")
]

let exec_cmd_opts = [
]

let arg_parser (s : string) : unit =
    match s with
    | "parse" -> cmd := Some Cmd_parse ; cmd_opts := parse_cmd_opts
    | "exec" -> cmd := Some Cmd_exec ; cmd_opts := exec_cmd_opts
    | _ -> arg := Some s

let parse_and_show (cmd : parse_cmd_t) (s : string) : unit =
    let parse_and_show' parser shower s =
      let lexbuf = Lexing.from_string s in
      try
        let exp = parser Lexer.read_token lexbuf in
        print_endline (shower exp)
      with
      | Parser.Error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        Printf.printf
          ("Parser error near line %d, character %d.\n")
          pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol)


    in

    match cmd with
    | Expr -> parse_and_show' Parser.terminated_exp Ast.Expression.show s
    | Stm -> parse_and_show' Parser.terminated_stm Ast.Stm.show s
    | Pgm -> parse_and_show' Parser.terminated_pgm Ast.Program.show s
    | PgmFile -> 
      In_channel.with_open_text s (fun inch ->
        parse_and_show' Parser.terminated_pgm Ast.Program.show
        (In_channel.input_all inch)
      )

let exec (s : string) : unit =
  try
    In_channel.with_open_text s (fun inch ->
      let lexbuf = Lexing.from_channel inch in
      try
        let p = Parser.terminated_pgm Lexer.read_token lexbuf in
        let () = Interp.Api.show_prompts := true in
        Interp.exec p
      with
      | Parser.Error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        Printf.printf
          ("Parser error near line %d, character %d.\n")
          pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol)
    )
  with
  | Interp.MultipleDeclaration x ->
    print_endline ("Error: variable '" ^ x ^ "' multiply declared.")
  | Interp.UnboundVariable x ->
    print_endline ("Error: variable '" ^ x ^ "' used but not declared.")
  | Interp.UndefinedFunction f ->
    print_endline 
      ("Error: undefined function '" ^ f ^ "' called but not defined.")


let () =
    Arg.parse_dynamic cmd_opts arg_parser usage ;
    match (!cmd, !arg) with
    | (Some Cmd_parse, Some s) ->
            parse_and_show !parse_cmd s
    | (Some Cmd_exec, Some s) -> exec s
    | _ ->
            Arg.usage !cmd_opts usage

