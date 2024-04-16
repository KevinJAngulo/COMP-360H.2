module Id = struct
    type t = string
    [@@deriving show]

    let compare = String.compare
end

module Expression = struct

    type binop =
        | Plus
        | Minus
        | Times
        | Div
        | Mod
        | And
        | Or
        | Eq
        | Ne
        | Lt
        | Le
        | Gt
        | Ge
        [@@deriving show]

    type t =
        | Var of Id.t
        | Num of int
        | Bool of bool
        | Str of string
        | Binop of binop*t*t
        | Assign of Id.t*t
        | Not of t
        | Neg of t
        | Call of Id.t * t list
        [@@deriving show]
end

module Stm = struct
    type t =
        | Skip
        | VarDec of (Id.t * Expression.t option) list
        | Expr of Expression.t
        | Block of t list
        | If of Expression.t*t*t
        | While of Expression.t*t
        | Return of Expression.t option
        [@@deriving show]
end

module Program = struct
    type fundef = FunDef of Id.t*Id.t list*Stm.t list
    [@@deriving show]

    type t = Pgm of fundef list
    [@@deriving show]
end
