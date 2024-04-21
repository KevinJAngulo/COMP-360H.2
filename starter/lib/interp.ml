(* COMP 360H Project 2:  Information-tracking interpreter for the language
 * Imp.
 *
 * Valery Corral and Kevin Angulo Lezama.
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

  (* New Value with a tyoe Value.prim x Label*)
  type t = New_V of prim * Label.t  

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
  (*This is supposedly where we store the outputs, but we won't use it as discussed with prof. Danner*)
  type out = Value.prim list 

  (*According to our semantics, we define the frame to be as follows*)
  type t = 
  | Envs of env list * out 
  | Return of Value.t * out

  (*We will keep the out channel empty as we only needed it to represent mathematically the Non-Interference Theoream *)
  let empty_out : out = [] 

  (* Add an output to the current frame's output list. We won't need this as explained by prof. Danner.

  let add_output (out : out) (value : Value.prim) : out =
    value :: out  

  let add_outputs (eta : t) (additional_out : out) : t =
    match eta with
    | Envs (envs, out) -> Envs (envs, out @ additional_out)  (* Append new outputs *)
    | Return (_, _) -> failwith "Cannot add outputs to a return frame"
  *)

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
 *
 * The API now checks whether a value is high or low and if it can either be printed or      UPDATE
 * raise a security error.
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
      let eta = Frame.Envs ([
        List.combine params vs |> List.to_seq |> IdentMap.of_seq
      ],Frame.empty_out) in
      let eta' = exec_many eta body context in
      begin
        match eta' with
        (* Assuming Frame.Return also includes an output list now *)
        | Frame.Return (v, _) -> v  
        | _ -> impossible "function returned with non-Return frame."
      end
    with
    | Not_found -> 
      try Api.do_call f vs  
      with
      | Api.ApiError _ -> raise @@ UndefinedFunction f
  
  and eval = function
    | Frame.Return _ -> fun _ -> impossible "Cannot evaluate in a Return frame."
    | Frame.Envs ([], _) -> fun _ -> impossible "exec with empty environment frame."
    | eta -> fun context -> function
      | E.Var x -> (Frame.lookup eta x, eta)
      | E.Num n -> (Value.create_labeled_value (Value.V_Int n) context, eta)
      | E.Bool b -> (Value.create_labeled_value (Value.V_Bool b) context, eta)
      | E.Str s -> (Value.create_labeled_value (Value.V_Str s) context, eta)
      | E.Assign (x, e) ->
        (* Retrieve the security label of the variable 'x' if it exists in the environment *)
        let (Value.New_V (v_prime, label_prime), eta') = eval eta context e in
        let current_label = 
          try 
            let Value.New_V (_, label) = Frame.lookup eta x in
            label
          with 
          (* Default to low if not found*)
          | UnboundVariable _ -> Label.L  
        in
        if current_label = Label.L && label_prime = Label.H then
          (* Raising an error if trying to assign a high-security value to a low-security variable. No secure upgrade*)
          raise SecurityError  
        else
          let new_val = Value.create_labeled_value v_prime label_prime in
          (new_val, Frame.set eta' x new_val)
      
      | E.Binop (op, e1, e2) ->
        let (v, eta') = eval eta context e1 in
        let (v', eta'') = eval eta' context e2 in
        (binop op v v', eta'')
      | E.Neg e ->
        let (v, eta') = eval eta context e in
        (
          match v with
            | Value.New_V (Value.V_Int n, lbl) -> (Value.create_labeled_value (Value.V_Int (-n)) lbl, eta')
            | _ -> raise (TypeError "Bad operand type for negation")
        )
      | E.Not e ->
        let (v, eta') = eval eta context e in
        (
          match v with
          | Value.New_V (Value.V_Bool b, lbl) -> (Value.create_labeled_value (Value.V_Bool (not b)) lbl, eta')
          | _ -> raise (TypeError "Bad operand type for logical not")
        )
      | E.Call(f, es) ->
        let (vs, eta') =
          List.fold_left
            (fun (acc_vs, acc_eta) exp ->
              let (v, updated_eta) = eval acc_eta context exp  
              in (v :: acc_vs, updated_eta))
            ([], eta)
            es
        in
        let result = do_call f (List.rev vs) context
        (* Return the result and the updated environment *)  
        in (result, eta')  
    

  (*Declares variables*)
  and do_decs  (eta : Frame.t) (decs : (Ast.Id.t * Ast.Expression.t option) list) (context : Label.t) : Frame.t =
    match decs with
    | [] -> eta
    | (x, None) :: decs ->
      (*Declares variables with Labels based on security context*)
      let eta' = Frame.declare eta x (Value.create_labeled_value Value.V_Undefined context) 
      in do_decs  eta' decs context
    | (x, Some e) :: decs ->
      let (v, eta') = eval  eta context e
      in let eta'' = Frame.declare eta' x v
      in do_decs  eta'' decs context

  and exec_one = function
  | Frame.Return _ -> fun _ -> impossible "exec with Return frame."
  | Frame.Envs ([], _) -> fun _ -> impossible "exec with empty environment frame."
  | eta -> fun context -> function
    | S.Skip -> eta
    | S.VarDec decs -> do_decs eta decs context
    | S.Expr e ->
      let (_, eta') = eval eta context e in eta'
    | S.Block ss ->
      let eta' = Frame.push eta in
      begin
        match exec_many eta' ss context with
        (* Return an empty output frame, since the output is irrelevant in the interpreter, as discussed with prof. Danner*)
        | Frame.Return (v, _) -> Frame.Return (v, Frame.empty_out)  
        (* Pop the top environment off after executing the block, returning to the previous environment *)
        | eta'' -> Frame.pop eta''  
      end
    | S.If(e, s1, s2) ->
      let (v, eta') = eval eta context e in
      begin 
        match v with
        | Value.New_V (Value.V_Bool true, lbl) ->
          let new_context = if lbl = Label.H then Label.H else context in
          exec_one eta' new_context s1
        | Value.New_V (Value.V_Bool false, lbl) ->
          let new_context = if lbl = Label.H then Label.H else context in
          exec_one eta' new_context s2
        | _ -> raise (TypeError "Conditional test not a boolean value")
      end
    | S.While(e, body) ->
      let rec dowhile eta =
        let (v, eta') = eval eta context e in
        match v with
        | Value.New_V (Value.V_Bool true, lbl) ->
          let new_context = if lbl = Label.H then Label.H else context in
          let eta'' = exec_one eta' new_context body in
          begin
            match eta'' with
            (* Return immediately if a return frame is encountered *)
            | Frame.Return _ as ret -> ret  
            (* Otherwise, continue looping *)
            | _ -> dowhile eta''  
          end
        (* Exit loop when condition is false *)
        | Value.New_V (Value.V_Bool false, _) -> eta'  
        | _ -> raise (TypeError "While test not a boolean value")
      in dowhile eta
    | S.Return (Some e) ->
      let (v, _) = eval eta context e in
      Frame.Return (v, Frame.empty_out)
    | S.Return None ->
      Frame.Return (Value.create_labeled_value Value.V_None context, Frame.empty_out)
    
(* Function to execute multiple statements within a given context and frame *)
  and exec_many (eta : Frame.t) (ss : Ast.Stm.t list) (context: Label.t) : Frame.t =
    match ss with
    | [] -> eta  
    | s :: ss ->
      begin 
        match exec_one eta context s with 
        | Frame.Return (v,_) -> Frame.Return (v,Frame.empty_out)  
        | eta' -> exec_many eta' ss context  
      end 
    in
      (* Set the security context for the main function to Low *)
      let main_context = Label.L  
    in
      let _ = eval Frame.base main_context (E.Call ("main", [])) in
      ()



        
