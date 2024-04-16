(* Lexer for Imp.
 * 
 * Much of this (especially string lexing) is taken directly from Minsky, Y.
 * and Madhavapeddy, A., *Real World OCaml*, 2nd ed., 2022, in particular the
 * "Parsing with Ocamllex and Menhiir" chapter, online at
 * https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html
 *
 * N. Danner
 *)

{
    open Parser

    exception SyntaxError of string
}

let digit = ['0'-'9']
let letter = ['A'-'Z'] | ['a'-'z']

let number = '-'? digit+
let bool = "true" | "false"
let ident = letter (letter | digit | "_")*

(* We don't include newline in whitespace, because we need to catch it
 * separately in order to update the line number in the lexer, for error
 * reporting.
 *)
let newline = '\n' | '\r' | "\r\n"
let whitespace = ( ' ' | '\t' )+

rule read_token =
    parse
    | "/*"          { read_comment 0 lexbuf ; read_token lexbuf }

    | "||"          { OR }
    | "&&"          { AND }
    | "="           { ASSIGN}
    | "=="          { EQ }
    | "!="          { NE }
    | "<"           { LT }
    | "<="          { LE }
    | ">"           { GT }
    | ">="          { GE }
    | "+"           { PLUS }
    | "-"           { MINUS }
    | "*"           { TIMES }
    | "/"           { DIV }
    | "%"           { MOD }
    | "!"           { NOT }

    | "("           { LPAREN }
    | ")"           { RPAREN }
    | "{"           { LBRACE }
    | "}"           { RBRACE }
    | ";"           { SEMI }
    | ","           { COMMA }
    | '"'           { read_string (Buffer.create 80) lexbuf }

    | "function"    { FUNCTION }
    
    | "skip"        { SKIP }
    | "var"         { VAR }
    | "if"          { IF }
    | "then"        { THEN }
    | "else"        { ELSE }
    | "while"       { WHILE }
    | "do"          { DO }
    | "return"      { RETURN }

    | number        { NUM (int_of_string (Lexing.lexeme lexbuf)) }
    | bool          { BOOL (bool_of_string (Lexing.lexeme lexbuf)) }
    | ident         { ID (Lexing.lexeme lexbuf) }

    | newline       { Lexing.new_line lexbuf ; read_token lexbuf }

    | whitespace    { read_token lexbuf }

    | eof           { EOF }

and read_comment n =
  parse
  | "*/"      { if n = 0 then () else read_comment (n-1) lexbuf }
  | "/*"      { read_comment (n+1) lexbuf }
  | newline   { Lexing.new_line lexbuf ; read_comment n lexbuf }
  | _         { read_comment n lexbuf }
  | eof       { raise (SyntaxError ("Comment is not terminated")) }

and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }

