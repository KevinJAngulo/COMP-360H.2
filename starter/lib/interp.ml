(* COMP 360H Project 2:  Information-tracking interpreter for the language
 * Imp.
 *
 * N. Danner
 *)

module E = Ast.Expression
module S = Ast.Stm

(* 'a IdentMap.t:  the type of maps from identifiers to 'a.
 *)
module IdentMap = Map.Make(Ast.Id)

(* MultipleDeclaration x is raised when x is declared more than once in a
 * block.
 *)
exception MultipleDeclaration of Ast.Id.t

(* UnboundVariable x is raised when x is used but not declared.
 *)
exception UnboundVariable of Ast.Id.t

(* UndefinedFunction f is raised when f is called but has not been defined.
 *)
exception UndefinedFunction of Ast.Id.t

(* TypeError s is raised when an operator or function is applied to operands
 * of the incorrect type.  s is any (hopefuly useful) message.
 *)
exception TypeError of string

(* SecurityError is raised when there is an information flow from a
 * high-security value (returned by get_*_s or prompt_*_s) to a low-security
 * output function (print_* or prompt_* ).
 *)
exception SecurityError

(* impossible s:  raises Failure ("Impossible: " ^ s).
 *)
let impossible (s : string) : 'a =
  failwith @@ "Impossible: " ^ s

(* Label *)
module Label = struct
  type t = H | L

  let to_string = function
    | H -> "High"
    | L -> "Low"
end


(* Values. *)

module Value = struct
  type prim = 
    | V_Undefined
    | V_None
    | V_Int of int
    | V_Bool of bool
    | V_Str of string

  type t = New_V of prim * Label.t  (* Use Label.t instead of defining it here *)

  let create_labeled_value prim label = New_V (prim, label)

  let label_of_value (New_V (_, label)) = label
  let prim_of_value (New_V (prim, _)) = prim

  let to_string (New_V (prim, label)) =
    let label_str = Label.to_string label in
    let prim_str = match prim with
      | V_Undefined -> "?"
      | V_None -> "None"
      | V_Int n -> string_of_int n
      | V_Bool b -> string_of_bool b
      | V_Str s -> s
    in
    Printf.sprintf "%s (%s)" prim_str label_str
end

module Frame = struct
  type env = Value.t IdentMap.t
  type out = Value.prim list

  type t = 
  | Envs of env list * out 
  | Return of Value.t * out

  let empty_out : out = []

  let base : t = Envs ([IdentMap.empty], empty_out)

  let lookup (frame : t) (x : Ast.Id.t) : Value.t =
    let rec lookup_in_envs envs =
      match envs with
      | [] -> raise @@ UnboundVariable x
      | env :: rest -> try IdentMap.find x env with Not_found -> lookup_in_envs rest
    in
    match frame with
    | Return _ -> raise @@ Failure "Cannot lookup in a return frame"
    | Envs (envs, _) -> lookup_in_envs envs

  let set (frame : t) (x : Ast.Id.t) (v : Value.t) : t =
    let rec set_in_envs envs =
      match envs with
      | [] -> raise @@ UnboundVariable x
      | env :: rest -> if IdentMap.mem x env then IdentMap.add x v env :: rest else env :: set_in_envs rest
    in
    match frame with
    | Return _ -> raise @@ Failure "Cannot set in a return frame"
    | Envs (envs, out) -> Envs (set_in_envs envs, out)

  let declare (frame : t) (x : Ast.Id.t) (v : Value.t) : t =
    match frame with
    | Return _ -> raise @@ Failure "Cannot declare in a return frame"
    | Envs (envs, out) ->
      match envs with
      | [] -> raise @@ Failure "Cannot declare in an empty frame"
      | env :: rest ->
        if IdentMap.mem x env then raise @@ MultipleDeclaration x
        else Envs (IdentMap.add x v env :: rest, out)

  let push (frame : t) : t =
    match frame with
    | Return _ -> raise @@ Failure "Cannot push to a return frame"
    | Envs (envs, out) -> Envs (IdentMap.empty :: envs, out)

  let pop (frame : t) : t =
    match frame with
    | Return _ -> raise @@ Failure "Cannot pop from a return frame"
    | Envs ([], _) -> raise @@ Failure "Cannot pop from an empty environment stack"
    | Envs (_ :: rest, out) -> Envs (rest, out)
end


(* An implementation of the I/O API.  This is a little bit complex, because
 * this one implementation allows for a few variations:
 * - The input and output channel can be set by the client (default to
 *   standard input and output).
 * - The display of prompts (for the prompt_* functions) can be turned off
 *   (default on).
 * These variations let us use this module for interactive use (use the
 * defaults) and testing (redirect the i/o channels to a programmatic stream
 * and turn off the display of prompts.
 *
 * A client makes changes to the defaults by setting `in_channel`,
 * `out_channel`, and `show_prompts`.
 *)
 module Api = struct
  exception ApiError of string
  exception SecurityError

  let in_channel : Scanf.Scanning.in_channel ref = ref Scanf.Scanning.stdin
  let out_channel : Out_channel.t ref = ref Out_channel.stdout
  let show_prompts : bool ref = ref true

  let output (oc : Out_channel.t) (s : string) : unit =
    Out_channel.output_string oc s ; 
    Out_channel.flush oc

  let outputnl (oc : Out_channel.t) (s : string) : unit =
    output oc (s ^ "\n")

  let mk_value prim label = Value.New_V (prim, label)
  let mk_none = mk_value Value.V_None Label.L

  let api : (Value.t list -> Value.t) IdentMap.t =
    IdentMap.empty
    |> IdentMap.add "print_bool" (fun vs ->
      match vs with
      | [Value.New_V (Value.V_Bool b, _)] ->  (* Prints regardless of label *)
          outputnl !out_channel (Bool.to_string b); mk_none
      | _ -> raise (TypeError "Bad argument type for print_bool")
      )
    |> IdentMap.add "print_bool_s" (fun vs ->
      match vs with
      | [Value.New_V (Value.V_Bool b, Label.H)] ->
          outputnl !out_channel (Bool.to_string b); mk_none
      | [Value.New_V (_, Label.L)] -> raise SecurityError
      | _ -> raise (TypeError "Bad argument type for print_bool_s")
      )
    (* Similar implementations for `print_int`, `print_str`, `get_int`, `get_bool`, etc. *)
    |> IdentMap.add "print_int" (fun vs ->
      match vs with
      | [Value.New_V (Value.V_Int n, _)] ->
          outputnl !out_channel (Int.to_string n); mk_none
      | _ -> raise (TypeError "Bad argument type for print_int")
      )
    |> IdentMap.add "print_int_s" (fun vs ->
      match vs with
      | [Value.New_V (Value.V_Int n, Label.H)] ->
          outputnl !out_channel (Int.to_string n); mk_none
      | [Value.New_V (_, Label.L)] -> raise SecurityError
      | _ -> raise (TypeError "Bad argument type for print_int_s")
      )
    |> IdentMap.add "print_str" (fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, _)] ->
          outputnl !out_channel s; mk_none
      | _ -> raise (TypeError "Bad argument type for print_str")
      )
    |> IdentMap.add "print_str_s" (fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, Label.H)] ->
          outputnl !out_channel s; mk_none
      | [Value.New_V (_, Label.L)] -> raise SecurityError
      | _ -> raise (TypeError "Bad argument type for print_str_s")
      )

  let do_call (f : string) (vs : Value.t list) : Value.t =
    try
      IdentMap.find f api vs
    with
    | Not_found -> raise (ApiError f)
end


(* binop op v v' = the result of applying the metalanguage operation
 * corresponding to `op` to v and v'.
 *)

(* Function to combine labels *)
let combine_labels l1 l2 = 
  if l1 = Label.H || l2 = Label.H then Label.H else Label.L

(* binop op v v' = the result of applying the binary operation `op` 
 * to values `v` and `v'`, resulting in a value with the combined security label. *)
let binop (op : E.binop) (v : Value.t) (v' : Value.t) : Value.t =
  let Value.New_V (p1, l1) = v in
  let Value.New_V (p2, l2) = v' in
  let combined_label = combine_labels l1 l2 in 
  match (op, p1, p2) with
  | (E.Plus, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Int (n + n'), combined_label)
  | (E.Minus, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Int (n - n'), combined_label)
  | (E.Times, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Int (n * n'), combined_label)
  | (E.Div, Value.V_Int n, Value.V_Int n') when n' != 0 ->
      Value.New_V (Value.V_Int (n / n'), combined_label)
  | (E.Mod, Value.V_Int n, Value.V_Int n') when n' != 0 ->
      Value.New_V (Value.V_Int (n mod n'), combined_label)
  | (E.And, Value.V_Bool b, Value.V_Bool b') ->
      Value.New_V (Value.V_Bool (b && b'), combined_label)
  | (E.Or, Value.V_Bool b, Value.V_Bool b') ->
      Value.New_V (Value.V_Bool (b || b'), combined_label)
  | (E.Eq, _, _) ->
      Value.New_V (Value.V_Bool (Value.prim_of_value v = Value.prim_of_value v'), combined_label)
  | (E.Ne, _, _) ->
      Value.New_V (Value.V_Bool (Value.prim_of_value v <> Value.prim_of_value v'), combined_label)
  | (E.Lt, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Bool (n < n'), combined_label)
  | (E.Le, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Bool (n <= n'), combined_label)
  | (E.Gt, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Bool (n > n'), combined_label)
  | (E.Ge, Value.V_Int n, Value.V_Int n') ->
      Value.New_V (Value.V_Bool (n >= n'), combined_label)
  | _ -> raise (TypeError "Incompatible operand types for binary operation")


(* If p : fundefs and lookup p f = (xs, ss), then f is the function with
 * parameters list xs and body ss.
 *)
type fundefs = ((Ast.Id.t list)*(Ast.Stm.t list)) IdentMap.t

(* preprocess [(FunDef(f_0, ps_0, body_0),...] = m, where
 * m[f_i] = (ps_i, body_i).
 *)
let preprocess (Ast.Program.Pgm p : Ast.Program.t) : fundefs =
  IdentMap.of_list @@
    List.map
      (fun (Ast.Program.FunDef (f, ps, body)) -> (f, (ps, body)))
      p

(* exec p:  execute the program p.
 *)
(* This function assumes that preprocess, Api.do_call, Frame and Value modules are defined elsewhere. *)
let exec (p : Ast.Program.t) : unit =
  (* Assuming preprocess is defined to parse the program *)
  let fs = preprocess p in

  let rec do_call (f : Ast.Id.t) (vs : Value.t list) (context : Label.t) : Value.t =
    try
      let (params, body) = IdentMap.find f fs in
      let initial_env = List.combine params vs |> List.to_seq |> IdentMap.of_seq in
      let eta = Frame.Envs ([initial_env], Frame.empty_out) in
      let eta' = exec_many context eta body in
      match eta' with
      | Frame.Return (v, _) -> v
      | _ -> impossible "Function returned with non-Return frame."
    with
    | Not_found -> 
      try Api.do_call f vs
      with
      | Api.ApiError _ -> raise (UndefinedFunction f)

  and eval (context : Label.t) (env : Frame.t) (expr : Ast.Expression.t) : Value.t * Frame.t =
    match env with
    | Frame.Return _ -> failwith "Cannot evaluate in a Return frame."
    | Frame.Envs _ as eta ->
        match expr with
        | E.Var x -> (Frame.lookup eta x, eta)
        | E.Num n -> (Value.create_labeled_value (Value.V_Int n) context, eta)
        | E.Bool b -> (Value.create_labeled_value (Value.V_Bool b) context, eta)
        | E.Str s -> (Value.create_labeled_value (Value.V_Str s) context, eta)
        | E.Assign (x, e) ->
            let (v, eta') = eval context eta e in
            (v, Frame.set eta' x v)
        | E.Binop (op, e1, e2) ->
            let (v, eta') = eval context eta e1 in
            let (v', eta'') = eval context eta' e2 in
            (binop op v v', eta'')
        | E.Neg e ->
            let (v, eta') = eval context eta e in
            (match v with
             | Value.New_V (Value.V_Int n, lbl) -> (Value.create_labeled_value (Value.V_Int (-n)) lbl, eta')
             | _ -> raise (TypeError "Bad operand type for negation"))
        | E.Not e ->
            let (v, eta') = eval context eta e in
            (match v with
             | Value.New_V (Value.V_Bool b, lbl) -> (Value.create_labeled_value (Value.V_Bool (not b)) lbl, eta')
             | _ -> raise (TypeError "Bad operand type for logical not"))
        | E.Call (f, es) ->
            let (vs, eta') = List.fold_right (fun e (acc, eta) -> let (v, eta') = eval context eta e in (v :: acc, eta')) es ([], eta) in
            let result = do_call f vs context in
            (result, eta')

  and exec_many (context : Label.t) (eta : Frame.t) (ss : Ast.Stm.t list) : Frame.t =
    List.fold_left (fun env s -> match exec_one context env s with
      | Frame.Return _ as ret -> ret
      | env' -> env') eta ss

  and exec_one (context : Label.t) (eta : Frame.t) (stmt : Ast.Stm.t) : Frame.t =
    match eta with
    | Frame.Return _ -> eta
    | Frame.Envs _ ->
        match stmt with
        | S.Skip -> eta
        | S.VarDec decs -> List.fold_left (fun eta (x, opt_e) -> 
            match opt_e with
            | None -> Frame.declare eta x (Value.create_labeled_value Value.V_Undefined Label.L)
            | Some e -> let (v, eta') = eval context eta e in Frame.declare eta' x v) eta decs
        | S.Expr e -> let (_, eta') = eval context eta e in eta'
        | S.Block ss -> let nested = Frame.push eta in let result = exec_many context nested ss in Frame.pop result
        | S.If (e, s1, s2) ->
            let (cond, eta') = eval context eta e in
            (match cond with
             | Value.New_V (Value.V_Bool true, _) -> exec_one context eta' s1
             | Value.New_V (Value.V_Bool false, _) -> exec_one context eta' s2
             | _ -> failwith "Non-boolean in if condition")
        | S.While (e, body) ->
            let rec loop env =
              let (cond, env') = eval context env e in
              match cond with
              | Value.New_V (Value.V_Bool true, _) -> loop (exec_one context env' body)
              | Value.New_V (Value.V_Bool false, _) -> env'
              | _ -> failwith "Non-boolean in while condition"
            in loop eta
        | S.Return (Some e) ->
            let (v, _) = eval context eta e in Frame.Return (v, Frame.empty_out)
        | S.Return None -> Frame.Return (Value.create_labeled_value Value.V_None Label.L, Frame.empty_out)

  in
  let main_context = Label.L  (* Initialize the main program with a Low security context *)
  in
  let _ = do_call "main" [] main_context  (* Call main with no arguments and Low context *)
  in
  ()
