
(* The type of tokens. *)

type token = 
  | WHILE
  | VAR
  | TIMES
  | THEN
  | STRING of (string)
  | SKIP
  | SEMI
  | RPAREN
  | RETURN
  | RBRACE
  | PLUS
  | OR
  | NUM of (int)
  | NOT
  | NE
  | MOD
  | MINUS
  | LT
  | LPAREN
  | LE
  | LBRACE
  | IF
  | ID of (string)
  | GT
  | GE
  | FUNCTION
  | EQ
  | EOF
  | ELSE
  | DO
  | DIV
  | COMMA
  | BOOL of (bool)
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val terminated_stm: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.Stm.t)

val terminated_pgm: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.Program.t)

val terminated_exp: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.Expression.t)
