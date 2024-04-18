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

  (* Add an output to the current frame's output list *)
  let add_output (out : out) (value : Value.prim) : out =
    value :: out  (* Append new output to the list *)
  let add_outputs (eta : t) (additional_out : out) : t =
    match eta with
    | Envs (envs, out) -> Envs (envs, out @ additional_out)  (* Append new outputs *)
    | Return (_, _) -> failwith "Cannot add outputs to a return frame"

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
    | Envs ([], _) -> raise @@ Failure "Cannot pop from an empty environment stack"
    | Envs (_ :: rest, out) -> Envs (rest, out)
    | Return _ -> raise @@ Failure "Cannot pop from a return frame"
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

  let api = [
    ("print_bool", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Bool b, Label.L)] -> 
        outputnl !out_channel (Bool.to_string b); Value.New_V (Value.V_None, Label.L)
      | [Value.New_V (_, Label.H)] -> 
        raise SecurityError
      | _ -> 
        raise (TypeError "Bad argument type for print_bool")
    );
    ("get_bool", fun vs ->
      match vs with
      | [] -> 
        Value.New_V (Value.V_Bool (Scanf.bscanf !in_channel " %B" Fun.id), Label.L)
      | _ -> 
        raise (TypeError "Bad argument type for get_bool")
    );
    ("prompt_bool", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, _)] ->
        if !show_prompts then output !out_channel s;
        Value.New_V (Value.V_Bool (Scanf.bscanf !in_channel " %B" Fun.id), Label.L)
      | _ -> 
        raise (TypeError "Bad argument type for prompt_bool")
    );
    ("print_int", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Int n, Label.L)] -> 
        outputnl !out_channel (Int.to_string n); Value.New_V (Value.V_None, Label.L)
      | [Value.New_V (_, Label.H)] -> 
        raise SecurityError
      | _ -> 
        raise (TypeError "Bad argument type for print_int")
    );
    ("get_int", fun vs ->
      match vs with
      | [] -> 
        Value.New_V (Value.V_Int (Scanf.bscanf !in_channel " %d" Fun.id), Label.L)
      | _ -> 
        raise (TypeError "Bad argument type for get_int")
    );
    ("prompt_int", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, _)] ->
        if !show_prompts then output !out_channel s;
        Value.New_V (Value.V_Int (Scanf.bscanf !in_channel " %d" Fun.id), Label.L)
      | _ -> 
        raise (TypeError "Bad argument type for prompt_int")
    );
    ("print_str", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, Label.L)] -> 
        outputnl !out_channel s; Value.New_V (Value.V_None, Label.L)
      | [Value.New_V (_, Label.H)] -> 
        raise SecurityError
      | _ -> 
        raise (TypeError "Bad argument type for print_str")
    );
    ("get_str", fun vs ->
      match vs with
      | [] -> 
        Value.New_V (Value.V_Str (Scanf.bscanf !in_channel "%s" Fun.id), Label.L)
      | _ -> 
        raise (TypeError "Bad argument type for get_str")
    );
    ("prompt_str", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, _)] ->
        if !show_prompts then output !out_channel s;
        Value.New_V (Value.V_Str (Scanf.bscanf !in_channel "%s" Fun.id), Label.L)
      | _ -> 
        raise (TypeError "Bad argument type for prompt_str")
    );
    ("print_bool_s", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Bool b, lbl)] -> 
        outputnl !out_channel (Bool.to_string b); Value.New_V (Value.V_None, lbl)
      | _ -> 
        raise (TypeError "Bad argument type for print_bool_s")
    );
    ("get_bool_s", fun vs ->
      match vs with
      | [] -> 
        Value.New_V (Value.V_Bool (Scanf.bscanf !in_channel " %B" Fun.id), Label.H)
      | _ -> 
        raise (TypeError "Bad argument type for get_bool_s")
    );
    ("prompt_bool_s", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, Label.H)] ->
        if !show_prompts then output !out_channel s;
        Value.New_V (Value.V_Bool (Scanf.bscanf !in_channel " %B" Fun.id), Label.H)
      | [Value.New_V (_, Label.L)] -> 
        raise SecurityError
      | _ -> 
        raise (TypeError "Bad argument type for prompt_bool_s")
    );
    ("print_int_s", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Int n, lbl)] -> 
        outputnl !out_channel (Int.to_string n); Value.New_V (Value.V_None, lbl)
      | _ -> 
        raise (TypeError "Bad argument type for print_int_s")
    );
    ("get_int_s", fun vs ->
      match vs with
      | [] -> 
        Value.New_V (Value.V_Int (Scanf.bscanf !in_channel " %d" Fun.id), Label.H)
      | _ -> 
        raise (TypeError "Bad argument type for get_int_s")
    );
    ("prompt_int_s", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, Label.H)] ->
        if !show_prompts then output !out_channel s;
        Value.New_V (Value.V_Int (Scanf.bscanf !in_channel " %d" Fun.id), Label.H)
      | [Value.New_V (_, Label.L)] -> 
        raise SecurityError
      | _ -> 
        raise (TypeError "Bad argument type for prompt_int_s")
    );
    ("print_str_s", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, lbl)] -> 
        outputnl !out_channel s; Value.New_V (Value.V_None, lbl)
      | _ -> 
        raise (TypeError "Bad argument type for print_str_s")
    );
    ("get_str_s", fun vs ->
      match vs with
      | [] -> 
        Value.New_V (Value.V_Str (Scanf.bscanf !in_channel "%s" Fun.id), Label.H)
      | _ -> 
        raise (TypeError "Bad argument type for get_str_s")
    );
    ("prompt_str_s", fun vs ->
      match vs with
      | [Value.New_V (Value.V_Str s, Label.H)] ->
        if !show_prompts then output !out_channel s;
        Value.New_V (Value.V_Str (Scanf.bscanf !in_channel "%s" Fun.id), Label.H)
      | [Value.New_V (_, Label.L)] -> 
        raise SecurityError
      | _ -> 
        raise (TypeError "Bad argument type for prompt_str_s")
    )
  ] |> List.to_seq |> IdentMap.of_seq


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

  let fs = preprocess p in  

  let rec do_call (f : Ast.Id.t) (vs : Value.t list) (context : Label.t) : Value.t =
    try
      let (params, body) = IdentMap.find f fs in
      let initial_env = List.combine params vs |> List.to_seq |> IdentMap.of_seq in
      let eta = Frame.Envs ([initial_env], Frame.empty_out)  (* Providing both arguments *)
      in
      let eta' = exec_many context eta body in
      match eta' with
      | Frame.Return (v, _) -> v  (* Assuming Frame.Return also includes an output list now *)
      | _ -> impossible "function returned with non-Return frame."
    with
    | Not_found -> 
      try Api.do_call f vs  (* Assuming Api.do_call does not handle context *)
      with
      | Api.ApiError _ -> raise (UndefinedFunction f)
  
  and eval context = function
  | Frame.Return _ -> failwith "Cannot evaluate in a Return frame."
  | Frame.Envs ([], _) -> failwith "exec with empty environment frame."
  | eta -> function
    | E.Var x -> 
      (Frame.lookup eta x, eta)
    | E.Num n -> 
      (Value.create_labeled_value (Value.V_Int n) context, eta)
    | E.Bool b -> 
      (Value.create_labeled_value (Value.V_Bool b) context, eta)
    | E.Str s -> 
      (Value.create_labeled_value (Value.V_Str s) context, eta)
    | E.Assign (x, e) ->
      let (v, eta') = eval context eta e in
      let (Value.New_V (prim, lbl)) = v in
      let new_val = Value.create_labeled_value prim lbl in
      (new_val, Frame.set eta' x new_val)
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
    | E.Call(f, es) ->
      let (vs, eta') = List.fold_right (fun e (acc, eta) -> 
        let (v, eta') = eval context eta e in (v :: acc, eta')) es ([], eta) in
      let result = do_call f vs context in
      (result, eta')
    

  and do_decs (context : Label.t) (eta : Frame.t) (decs : (Ast.Id.t * Ast.Expression.t option) list) : Frame.t =
  match decs with
  | [] -> eta
  | (x, None) :: decs ->
    let eta' = Frame.declare eta x (Value.create_labeled_value Value.V_Undefined context)
    in do_decs context eta' decs
  | (x, Some e) :: decs ->
    let (v, eta') = eval context eta e 
    in let eta'' = Frame.declare eta' x v
    in do_decs context eta'' decs

  and exec_one context = function
  | Frame.Return _ -> impossible "exec with Return frame."
  | Frame.Envs ([], _) -> impossible "exec with empty environment frame."
  | eta -> function
    | S.Skip -> eta
    | S.VarDec decs -> do_decs context eta decs
    | S.Expr e ->
      let (_, eta') = eval context eta e in
      eta'
    | S.Block ss ->
      let nested = Frame.push eta in
      let result = exec_many context nested ss in
      Frame.pop result
    | S.If(e, s1, s2) ->
      let (v, eta') = eval context eta e in
      begin
        match v with
        | Value.New_V (Value.V_Bool true, lbl) ->
          let new_context = if lbl = Label.H then Label.H else context in
          exec_one new_context eta' s1
        | Value.New_V (Value.V_Bool false, lbl) ->
          let new_context = if lbl = Label.H then Label.H else context in
          exec_one new_context eta' s2
        | _ -> raise (TypeError "Conditional test not a boolean value")
      end
    | S.While(e, body) ->
      let rec dowhile eta =
        let (v, eta') = eval context eta e in
        match v with
        | Value.New_V (Value.V_Bool true, lbl) ->
          let new_context = if lbl = Label.H then Label.H else context in
          dowhile (exec_one new_context eta' body)
        | Value.New_V (Value.V_Bool false, _) -> eta'
        | _ -> raise (TypeError "While test not a boolean value")
      in dowhile eta
    | S.Return (Some e) ->
      let (v, _) = eval context eta e in
      Frame.Return (v, Frame.empty_out)
    | S.Return None ->
      Frame.Return (Value.create_labeled_value Value.V_None context, Frame.empty_out)
  
        
        
        
(* Function to execute multiple statements within a given context and starting frame *)
and exec_many context (eta : Frame.t) (ss : Ast.Stm.t list) : Frame.t =
  match ss with
  | [] -> eta
  | s :: ss ->
    match exec_one context eta s with
    | Frame.Return _ as ret -> ret  (* If a return frame is encountered, propagate it up immediately *)
    | eta' -> exec_many context eta' ss  (* Otherwise, continue executing the remaining statements *)
  in
(* Main entry point of the program, setting the initial context and executing the main function *)
  let main_context = Label.L  (* Set the security context for the main function to Low *)
  in
  let _ = eval main_context Frame.base (E.Call ("main", [])) in (* Evaluates the call to main function *)
  ()


        
