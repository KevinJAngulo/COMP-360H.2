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

(* Values.
 *)
module Value = struct
  type prim = 
    | V_Undefined
    | V_None
    | V_Int of int
    | V_Bool of bool
    | V_Str of string

  type label = H | L

  type t = New_V of prim * label

  let label_of_value = function
    | New_V (_, label) -> label

  let prim_of_value = function
    | New_V (prim, _) -> prim


  let create_labeled_value prim label = New_V (prim, label)

  let to_string = function
    | New_V (prim, label) ->
      let label_str = match label with H -> "High" | L -> "Low" in
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

  type t = Envs of env list * out | Return of Value.t * out

  let empty_out : out = []

  let base : t = Envs ([IdentMap.empty], empty_out)

  let to_string (frame : t) : string =
    match frame with
    | Return (v, out) -> Printf.sprintf "Return: %s, Output: [%s]" (Value.to_string v) (String.concat ", " (List.map Value.to_string out))
    | Envs (envs, out) ->
      let envs_str = envs |> List.map IdentMap.to_list
                          |> List.map (fun l -> String.concat ", " (List.map (fun (id, v) -> Printf.sprintf "%s: %s" id (Value.to_string v)) l))
                          |> String.concat "; "
      in Printf.sprintf "Environments: [%s], Output: [%s]" envs_str (String.concat ", " (List.map Value.to_string out))

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

  let in_channel : Scanf.Scanning.in_channel ref = ref Scanf.Scanning.stdin
  let out_channel : Out_channel.t ref = ref Out_channel.stdout
  let show_prompts : bool ref = ref true

  let output (oc : Out_channel.t) (s : string) : unit =
    Out_channel.output_string oc s;
    Out_channel.flush oc

  let outputnl (oc : Out_channel.t) (s : string) : unit =
    output oc (s ^ "\n")

  (* Define the map type properly: a map from string to functions that take a list of Value.t and return Value.t *)
  let api : (Value.t list -> Value.t) IdentMap.t =
    let add_func map (key, func) = IdentMap.add key func map in
    List.fold_left add_func IdentMap.empty [
      ("print_bool", fun vs ->
        match vs with
        | [Value.New_V (Value.V_Bool n, _)] ->
          outputnl (!out_channel) (Bool.to_string n); Value.New_V (Value.V_None, Value.L)
        | _ -> raise @@ TypeError "Bad argument type for print_bool"
      );
      ("get_bool", fun vs ->
        match vs with
        | [] -> Value.New_V (Value.V_Bool (Scanf.bscanf !in_channel " %B" (fun b -> b)), Value.L)
        | _ -> raise @@ TypeError "Bad argument type for get_bool"
      );
      ("prompt_bool", fun vs ->
        match vs with
        | [Value.New_V (Value.V_Str s, _)] ->
          if !show_prompts then output (!out_channel) s else ();
          Value.New_V (Value.V_Bool (Scanf.bscanf !in_channel " %B" (fun b -> b)), Value.L)
        | _ -> raise @@ TypeError "Bad argument type for prompt_bool"
      );
      ("print_int", fun vs ->
        match vs with
        | [Value.New_V (Value.V_Int n, _)] ->
          outputnl (!out_channel) (Int.to_string n); Value.New_V (Value.V_None, Value.L)
        | _ -> raise @@ TypeError "Bad argument type for print_int"
      );
      ("get_int", fun vs ->
        match vs with
        | [] -> Value.New_V (Value.V_Int (Scanf.bscanf !in_channel " %d" (fun n -> n)), Value.L)
        | _ -> raise @@ TypeError "Bad argument type for get_int"
      );
      ("print_str", fun vs ->
        match vs with
        | [Value.New_V (Value.V_Str s, _)] ->
          outputnl (!out_channel) s; Value.New_V (Value.V_None, Value.L)
        | _ -> raise @@ TypeError "Bad argument type for print_str"
      );
      ("get_str", fun vs ->
        match vs with
        | [] -> Value.New_V (Value.V_Str (Scanf.bscanf !in_channel "%s" (fun s -> s)), Value.L)
        | _ -> raise @@ TypeError "Bad argument type for get_str"
      );
      ("prompt_str", fun vs ->
        match vs with
        | [Value.New_V (Value.V_Str s, _)] ->
          if !show_prompts then output (!out_channel) s else ();
          Value.New_V (Value.V_Str (Scanf.bscanf !in_channel " %s" (fun s -> s)), Value.L)
        | _ -> raise @@ TypeError "Bad argument type for prompt_str"
      )
    ]

  let do_call (f : string) (vs : Value.t list) : Value.t =
    try
      IdentMap.find f api vs
    with
    | Not_found -> raise @@ ApiError f
end



(* binop op v v' = the result of applying the metalanguage operation
 * corresponding to `op` to v and v'.
 *)

(* Function to combine labels *)
let combine_labels l1 l2 l3 = 
  if l1 = Value.H || l2 = Value.H || l3 = Value.H then Value.H else Value.L

(* binop op context v v' = the result of applying the binary operation `op` 
 * to values `v` and `v'` under the given security context `context`, resulting in
 * a value with the combined security label. *)
let binop (op : E.binop) (context : Value.label) (v : Value.t) (v' : Value.t) : Value.t =
  match (v, v') with
  | (Value.New_V (Value.V_Int n, l1), Value.New_V (Value.V_Int n', l2)) ->
      let combined_label = combine_labels context l1 l2 in
      begin match op with
      | E.Plus  -> Value.New_V (Value.V_Int (n + n'), combined_label)
      | E.Minus -> Value.New_V (Value.V_Int (n - n'), combined_label)
      | E.Times -> Value.New_V (Value.V_Int (n * n'), combined_label)
      | E.Div   -> if n' != 0 then Value.New_V (Value.V_Int (n / n'), combined_label) 
                   else raise (TypeError "Division by zero")
      | E.Mod   -> if n' != 0 then Value.New_V (Value.V_Int (n mod n'), combined_label) 
                   else raise (TypeError "Modulo by zero")
      | _ -> raise (TypeError "Incompatible types for binop")
      end
  | (Value.New_V (Value.V_Bool b, l1), Value.New_V (Value.V_Bool b', l2)) ->
      let combined_label = combine_labels context l1 l2 in
      begin match op with
      | E.And -> Value.New_V (Value.V_Bool (b && b'), combined_label)
      | E.Or  -> Value.New_V (Value.V_Bool (b || b'), combined_label)
      | E.Eq  -> Value.New_V (Value.V_Bool (b = b'), combined_label)
      | E.Ne  -> Value.New_V (Value.V_Bool (b <> b'), combined_label)
      | _ -> raise (TypeError "Incompatible types for binop")
      end
  | (Value.New_V (Value.V_Int n, l1), Value.New_V (Value.V_Int n', l2)) ->
      let combined_label = combine_labels context l1 l2 in
      begin match op with
      | E.Lt -> Value.New_V (Value.V_Bool (n < n'), combined_label)
      | E.Le -> Value.New_V (Value.V_Bool (n <= n'), combined_label)
      | E.Gt -> Value.New_V (Value.V_Bool (n > n'), combined_label)
      | E.Ge -> Value.New_V (Value.V_Bool (n >= n'), combined_label)
      | _ -> raise (TypeError "Incompatible types for binop")
      end
  | _ -> raise (TypeError "Incompatible or unsupported types for binop")



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
  let fs = preprocess p in  (* assuming preprocess is defined to parse the program *)

  let rec do_call (f : Ast.Id.t) (vs : Value.t list) : Value.t =
    try
      let (params, body) = IdentMap.find f fs in
      let env = Frame.Envs [List.combine params vs |> List.to_seq |> IdentMap.of_seq] in
      match exec_many env body with
      | Frame.Return v -> v
      | _ -> failwith "Function did not return properly."
    with
    | Not_found -> Api.do_call f vs  (* assuming Api.do_call is defined to handle external API calls *)

  and eval (env : Frame.t) (expr : Ast.Expr.t) : Value.t * Frame.t =
    match env with
    | Frame.Return _ -> failwith "Cannot evaluate in a Return frame."
    | Frame.Envs _ as eta -> (
        match expr with
        | E.Var x -> (Frame.lookup eta x, eta)
        | E.Num n -> (Value.V_Int n, eta)  (* Assuming Value.V_Int is a valid constructor *)
        | E.Bool b -> (Value.V_Bool b, eta)  (* Assuming Value.V_Bool is a valid constructor *)
        | E.Str s -> (Value.V_Str s, eta)  (* Assuming Value.V_Str is a valid constructor *)
        | E.Assign (x, e) ->
            let (v, eta') = eval eta e in
            (v, Frame.set eta' x v)
        | E.Binop (op, e1, e2) ->
            let (v, eta') = eval eta e1 in
            let (v', eta'') = eval eta' e2 in
            (binop op v v', eta'')  (* Assuming binop is defined elsewhere *)
        | E.Neg e ->
            let (v, eta') = eval eta e in
            (match v with Value.V_Int n -> (Value.V_Int (-n), eta') | _ -> raise @@ TypeError "Bad operand type for negation")
        | E.Not e ->
            let (v, eta') = eval eta e in
            (match v with Value.V_Bool b -> (Value.V_Bool (not b), eta') | _ -> raise @@ TypeError "Bad operand type for logical not")
        | E.Call (f, es) ->
            let (vs, eta') = List.fold_right (fun e (acc, eta) -> let (v, eta') = eval eta e in (v :: acc, eta')) es ([], eta) in
            let result = do_call f (List.rev vs) in
            (result, eta')
      )

  and exec_one (eta : Frame.t) (stmt : Ast.Stm.t) : Frame.t =
    match eta with
    | Frame.Return _ -> eta
    | Frame.Envs _ ->
        match stmt with
        | S.Skip -> eta
        | S.VarDec decs -> List.fold_left (fun eta (x, opt_e) -> 
            match opt_e with
            | None -> Frame.declare eta x Value.V_Undefined  (* Assuming Value.V_Undefined is a valid constructor *)
            | Some e -> let (v, eta') = eval eta e in Frame.declare eta' x v) eta decs
        | S.Expr e -> let (_, eta') = eval eta e in eta'
        | S.Block ss -> let nested = Frame.push eta in let result = exec_many nested ss in Frame.pop result
        | S.If (e, s1, s2) ->
            let (cond, eta') = eval eta e in
            (match cond with Value.V_Bool true -> exec_one eta' s1 | Value.V_Bool false -> exec_one eta' s2 | _ -> failwith "Non-boolean in if condition")
        | S.While (e, body) ->
            let rec loop env =
              let (cond, env') = eval env e in
              match cond with
              | Value.V_Bool true -> loop (exec_one env' body)
              | Value.V_Bool false -> env'
              | _ -> failwith "Non-boolean in while condition"
            in loop eta
        | S.Return (Some e) ->
            let (v, _) = eval eta e in Frame.Return v
        | S.Return None -> Frame.Return Value.V_None

  and exec_many (eta : Frame.t) (ss : Ast.Stm.t list) : Frame.t =
    List.fold_left (fun env s -> match exec_one env s with
      | Frame.Return _ as ret -> ret
      | env' -> env') eta ss

  in
  let _ = eval (Frame.base) (E.Call ("main", [])) in  (* assuming Frame.base is defined and E.Call is the correct constructor *)
  ()
