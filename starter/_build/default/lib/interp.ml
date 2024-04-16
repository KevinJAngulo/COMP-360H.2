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
  (* PrimValue *)
  type prim = 
    | V_Undefined
    | V_None  (* Direct representation as a primitive for easier API handling *)
    | V_Int of int
    | V_Bool of bool
    | V_Str of string
    [@@deriving show]

  (* Labels *)
  type label =
    | H  (* High *)
    | L  (* Low *)

  (* NewVal combines a PrimValue with a Label to form a new type Value *)
  type t =
    | New_V of prim * label  (* Represents values with associated security labels *)

  (* Conversion of PrimValue to string *)
  let prim_to_string p =
    match p with
    | V_Undefined -> "?"
    | V_None -> "None"
    | V_Int n -> string_of_int n
    | V_Bool b -> string_of_bool b
    | V_Str s -> s

  (* Conversion of Label to string *)
  let label_to_string l =
    match l with
    | H -> "High"
    | L -> "Low"

  (* Conversion of New_V to string *)
  let to_string (v : t) : string =
    match v with
    | New_V (prim, label) ->
      Printf.sprintf "%s (%s)" (prim_to_string prim) (label_to_string label)
end



module Frame = struct
  (* Definitions based on the new Value module *)
  type env = Value.t IdentMap.t
  type out = Value.t list

  (* Frame now includes environments paired with an output list or a return value paired with an output list. *)
  type t = Envs of env list * out | Return of Value.t * out

  (* Empty output list as the base output for new frames. *)
  let empty_out : out = []

  (* A base environment frame with an empty output list. *)
  let base : t = Envs ([IdentMap.empty], empty_out)

  (* Converts the Frame to a string, incorporating the new Value structure. *)
  let to_string (frame : t) : string =
    match frame with
    | Return (v, out) -> Printf.sprintf "Return: %s, Output: [%s]" (Value.to_string v) (String.concat ", " (List.map Value.to_string out))
    | Envs (envs, out) ->
      let envs_str = envs |> List.map IdentMap.to_list
                          |> List.map (fun l ->
                              String.concat ", " (List.map (fun (id, v) -> Printf.sprintf "%s: %s" id (Value.to_string v)) l))
                          |> String.concat "; "
      in Printf.sprintf "Environments: [%s], Output: [%s]" envs_str (String.concat ", " (List.map Value.to_string out))

  (* Updated lookup function for the new frame structure. *)
  let lookup (frame : t) (x : Ast.Id.t) : Value.t =
    let rec lookup_in_envs envs =
      match envs with
      | [] -> raise @@ UnboundVariable x
      | env :: rest ->
        try IdentMap.find x env
        with Not_found -> lookup_in_envs rest
    in
    match frame with
    | Return _ -> raise @@ Failure "Cannot lookup in a return frame"
    | Envs (envs, _) -> lookup_in_envs envs

  (* Set function updated for the new frame structure. *)
  let set (frame : t) (x : Ast.Id.t) (v : Value.t) : t =
    let rec set_in_envs envs =
      match envs with
      | [] -> raise @@ UnboundVariable x
      | env :: rest ->
        if IdentMap.mem x env
        then IdentMap.add x v env :: rest
        else env :: set_in_envs rest
    in
    match frame with
    | Return _ -> raise @@ Failure "Cannot set in a return frame"
    | Envs (envs, out) -> Envs (set_in_envs envs, out)

  (* Declare a new variable in the most recent environment. *)
  let declare (frame : t) (x : Ast.Id.t) (v : Value.t) : t =
    match frame with
    | Return _ -> raise @@ Failure "Cannot declare in a return frame"
    | Envs (envs, out) ->
      match envs with
      | [] -> raise @@ Failure "Cannot declare in an empty frame"
      | env :: rest ->
        if IdentMap.mem x env
        then raise @@ MultipleDeclaration x
        else Envs (IdentMap.add x v env :: rest, out)

  (* Push a new empty environment to the frame. *)
  let push (frame : t) : t =
    match frame with
    | Return _ -> raise @@ Failure "Cannot push to a return frame"
    | Envs (envs, out) -> Envs (IdentMap.empty :: envs, out)

  (* Pop the most recent environment from the frame. *)
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

  (* Raised when a function is invoked that is not in the API.
   *)
  exception ApiError of string

  (* in_channel:  input channel (for get_*, prompt_* ).
   *)
  let in_channel : Scanf.Scanning.in_channel ref = 
    ref Scanf.Scanning.stdin

  (* out_channel:  output channel (for print_*, prompt_* when prompts are
   * displayed).
   *)
  let out_channel : Out_channel.t ref = ref Out_channel.stdout

  (* show_prompts:  true to display prompts, false to not display.
   *)
  let show_prompts : bool ref = ref true

  (* output oc s:  output `s` to `oc` and flush `oc`.
   *)
  let output (oc : Out_channel.t) (s : string) : unit =
    Out_channel.output_string oc s ;
    Out_channel.flush oc

  (* outputnl oc s = output `s ^ '\n'` to `oc` and flush `oc`.
   *)
  let outputnl (oc : Out_channel.t) (s : string) : unit =
    output oc (s ^ "\n")

  (* The API definition.  The API is specified by a
   * (string*(Value.t->Value.t)) list.  Each element names an API function
   * and provides the code to be executed when the function is called.
   *)
  let api : (Value.t list -> Value.t) IdentMap.t =
    [
      ("print_bool", fun vs ->
        match vs with
        | [Value.V_Bool n] -> 
          outputnl (!out_channel) (Bool.to_string n) ; Value.V_None
        | _ -> raise @@ TypeError "Bad argument type for print_bool"
      )
    ; ("get_bool", fun vs ->
        match vs with
        | [] -> Value.V_Bool (Scanf.bscanf !in_channel " %B" (fun b -> b))
        | _ -> raise @@ TypeError "Bad argument type for get_bool"
      )
    ; ("prompt_bool", fun vs ->
        match vs with
        | [Value.V_Str s] ->
          if !show_prompts then output (!out_channel) s else () ;
            Value.V_Bool (Scanf.bscanf !in_channel " %B" (fun b -> b))
        | _ -> raise @@ TypeError "Bad argument type for prompt_bool"
      )
    ; ("print_int", fun vs ->
        match vs with
        | [Value.V_Int n] -> 
          outputnl (!out_channel) (Int.to_string n) ; Value.V_None
        | _ -> raise @@ TypeError "Bad argument type for print_int"
      )
    ; ("get_int", fun vs ->
        match vs with
        | [] -> Value.V_Int (Scanf.bscanf !in_channel " %d" (fun n -> n))
        | _ -> raise @@ TypeError "Bad argument type for get_int"
      )
    ; ("prompt_int", fun vs ->
        match vs with
        | [Value.V_Str s] ->
          if !show_prompts then output (!out_channel) s else () ;
            Value.V_Int (Scanf.bscanf !in_channel " %d" (fun n -> n))
        | _ -> raise @@ TypeError "Bad argument type for prompt_int"
      )
    ; ("print_str", fun vs ->
         match vs with
         | [Value.V_Str s] -> 
           outputnl (!out_channel) s ; Value.V_None
         | _ -> raise @@ TypeError "Bad argument type for print_s"
      )
    ; ("get_str", fun vs ->
        match vs with
        | [] -> Value.V_Str (Scanf.bscanf !in_channel "%s" (fun s -> s))
        | _ -> raise @@ TypeError "Bad argument type for get_str"
      )
    ; ("prompt_str", fun vs ->
        match vs with
        | [Value.V_Str s] ->
          if !show_prompts then output (!out_channel) s else () ;
            Value.V_Str (Scanf.bscanf !in_channel " %s" (fun s -> s))
        | _ -> raise @@ TypeError "Bad argument type for prompt_str"
      )
    ; ("print_bool_s", fun vs ->
        match vs with
        | [Value.V_Bool n] -> 
          outputnl (!out_channel) (Bool.to_string n) ; Value.V_None
        | _ -> raise @@ TypeError "Bad argument type for print_bool_s"
      )
    ; ("get_bool_s", fun vs ->
        match vs with
        | [] -> Value.V_Bool (Scanf.bscanf !in_channel " %B" (fun b -> b))
        | _ -> raise @@ TypeError "Bad argument type for get_bool_s"
      )
    ; ("prompt_bool_s", fun vs ->
        match vs with
        | [Value.V_Str s] ->
          if !show_prompts then output (!out_channel) s else () ;
            Value.V_Bool (Scanf.bscanf !in_channel " %B" (fun b -> b))
        | _ -> raise @@ TypeError "Bad argument type for prompt_bool_s"
      )
    ; ("print_int_s", fun vs ->
        match vs with
        | [Value.V_Int n] -> 
          outputnl (!out_channel) (Int.to_string n) ; Value.V_None
        | _ -> raise @@ TypeError "Bad argument type for print_int_s"
      )
    ; ("get_int_s", fun vs ->
        match vs with
        | [] -> Value.V_Int (Scanf.bscanf !in_channel " %d" (fun n -> n))
        | _ -> raise @@ TypeError "Bad argument type for get_int_s"
      )
    ; ("prompt_int_s", fun vs ->
        match vs with
        | [Value.V_Str s] ->
          if !show_prompts then output (!out_channel) s else () ;
            Value.V_Int (Scanf.bscanf !in_channel " %d" (fun n -> n))
        | _ -> raise @@ TypeError "Bad argument type for prompt_int_s"
      )
    ; ("print_str_s", fun vs ->
         match vs with
         | [Value.V_Str s] -> 
           outputnl (!out_channel) s ; Value.V_None
         | _ -> raise @@ TypeError "Bad argument type for print_str_s"
      )
    ; ("get_str_s", fun vs ->
        match vs with
        | [] -> Value.V_Str (Scanf.bscanf !in_channel "%s" (fun s -> s))
        | _ -> raise @@ TypeError "Bad argument type for get_str_s"
      )
    ; ("prompt_str_s", fun vs ->
        match vs with
        | [Value.V_Str s] ->
          if !show_prompts then output (!out_channel) s else () ;
            Value.V_Str (Scanf.bscanf !in_channel " %s" (fun s -> s))
        | _ -> raise @@ TypeError "Bad argument type for prompt_str_s"
      )
    ] |> List.to_seq |> IdentMap.of_seq

  (* do_call f vs invokes the API function corresponding to `f` with argument
   * list `vs`.
   *
   * Raises ApiError f: if f is not an API function.
   *)
  let do_call (f : string) (vs : Value.t list) : Value.t =
    try
      IdentMap.find f api vs
    with
    | Not_found -> raise @@ ApiError f


end

(* binop op v v' = the result of applying the metalanguage operation
 * corresponding to `op` to v and v'.
 *)
 let binop (context : Value.label) (op : E.binop) (v : Value.t) (v' : Value.t) : Value.t =
  let error_message = "Can't operate with two different labels under high security context." in

  let combine_labels l1 l2 =
    match context with
    | Value.High ->
      if l1 <> l2 then raise (TypeError error_message)
      else Value.High
    | Value.Low ->
      if l1 = Value.High || l2 = Value.High then Value.High
      else Value.Low
  in

  match (op, v, v') with
  | (E.Plus, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Int (n + n'), combine_labels l l')
  | (E.Minus, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Int (n - n'), combine_labels l l')
  | (E.Times, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Int (n * n'), combine_labels l l')
  | (E.Div, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) when n' != 0 ->
      Value.V_Prim (Value.P_Int (n / n'), combine_labels l l')
  | (E.Mod, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) when n' != 0 ->
      Value.V_Prim (Value.P_Int (n mod n'), combine_labels l l')
  | (E.And, Value.V_Prim (Value.P_Bool b, l), Value.V_Prim (Value.P_Bool b', l')) ->
      Value.V_Prim (Value.P_Bool (b && b'), combine_labels l l')
  | (E.Or, Value.V_Prim (Value.P_Bool b, l), Value.V_Prim (Value.P_Bool b', l')) ->
      Value.V_Prim (Value.P_Bool (b || b'), combine_labels l l')
  | (E.Eq, v, v') -> Value.V_Prim (Value.P_Bool (v = v'), combine_labels (Value.label_of v) (Value.label_of v'))
  | (E.Ne, v, v') -> Value.V_Prim (Value.P_Bool (v <> v'), combine_labels (Value.label_of v) (Value.label_of v'))
  | (E.Lt, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Bool (n < n'), combine_labels l l')
  | (E.Le, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Bool (n <= n'), combine_labels l l')
  | (E.Gt, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Bool (n > n'), combine_labels l l')
  | (E.Ge, Value.V_Prim (Value.P_Int n, l), Value.V_Prim (Value.P_Int n', l')) ->
      Value.V_Prim (Value.P_Bool (n >= n'), combine_labels l l')
  | _ -> raise @@
         TypeError (
           Printf.sprintf "Bad operand types or division by zero: %s %s %s"
             (Value.to_string v) (E.show_binop op) (Value.to_string v')
         )

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
let exec (p : Ast.Program.t) : unit =

  (* fs[f] = ([x_0,...,x_{n-1}], ss), where the program has a function
   * definition of the form
   *   function f(x_0,...,x_{n-1}) {
   *     ss
   *   }
   *)
  let fs = preprocess p in

  (*  do_call f [v_0,...,v_{n-1}] = v, where
   *    exec_many η body = Return v, where
   *    η = Env [{...,x_i → v_i,...}], where
   *    fs[f] = ([x_0,...,x_{n-1}], body),     if f ∈ dom fs
   *  = Api.do_call f vs,                      otherwise
   *)
  let rec do_call (f : Ast.Id.t) (vs : Value.t list) : Value.t =
    try
      let (params, body) = IdentMap.find f fs in
      let eta = Frame.Envs [
        List.combine params vs |> List.to_seq |> IdentMap.of_seq
      ] in
      let eta' = exec_many eta body in
      begin
        match eta' with
        | Frame.Return v -> v
        | _ -> impossible "function returned with non-Return frame."
      end
    with
    | Not_found -> 
      try Api.do_call f vs with
      | Api.ApiError _ -> raise @@ UndefinedFunction f

  (* eval η e = (v, η'), where η ├ e ↓ (v, η').
   *
   * Raises:  Failure if η is a return frame or empty environment frame.
   *)
  and eval = function
    | Frame.Return _ -> fun _ -> impossible "eval with Return frame."
    | Frame.Envs [] -> fun _ -> impossible "exec with empty environment frame."
    | eta -> function
      | E.Var x -> (Frame.lookup eta x, eta)
      | E.Num n -> (Value.V_Int n, eta)
      | E.Bool b -> (Value.V_Bool b, eta)
      | E.Str s -> (Value.V_Str s, eta)
      | E.Assign (x, e) ->
        let (v, eta') = eval eta e
        in (v, Frame.set eta' x v)
      | E.Binop (op, e, e') ->
        let (v, eta') = eval eta e in
        let (v', eta'') = eval eta' e' in
        (binop op v v', eta'')
      | E.Neg e ->
        let (v, eta') = eval eta e in
        (
          match v with
          | Value.V_Int n -> (Value.V_Int (-n), eta')
          | _ -> raise @@
                 TypeError (
                   Printf.sprintf "Bad operand type: -%s" 
                     (Value.to_string v)
                 )
        )
      | E.Not e ->
        let (v, eta') = eval eta e in
        (
          match v with
          | Value.V_Bool b -> (Value.V_Bool (not b), eta')
          | _ -> raise @@
                 TypeError (
                   Printf.sprintf "Bad operand type: !%s" 
                     (Value.to_string v)
                 )
        )
      | E.Call(f, es) ->
        let (vs, eta') =
          List.fold_left
            (fun (vs, eta) e -> let (v, eta') = eval eta e in (v :: vs, eta'))
            ([], eta)
            es
        in (do_call f (List.rev vs), eta')

  (* do_decs η [..., (x, Some e), ...] = η'', where η'' is obtained by adding
   * x → v to η', where η ├ e ↓ (v, η').
   * do_decs η [..., (x, None), ...] = η'', where η'' is obtained by adding
   * x → ? to η.
   *)
  and do_decs 
      (eta : Frame.t) 
      (decs : (Ast.Id.t * Ast.Expression.t option) list) : Frame.t =
    match decs with
    | [] -> eta
    | (x, None) :: decs -> 
      let eta' = Frame.declare eta x V_Undefined in
      do_decs eta' decs
    | (x, Some e) :: decs ->
      let (v, eta') = eval eta e in 
      let eta'' = Frame.declare eta' x v in
      do_decs eta'' decs

  (* exec_one η s = η', where s ├ η → η'.
   *)
  and exec_one = function
    | Frame.Return _ -> fun _ -> impossible "exec with Return frame."
    | Frame.Envs [] -> fun _ -> impossible "exec with empty environment frame."
    | eta -> function
      | S.Skip -> eta
      | S.VarDec decs -> do_decs eta decs
      | S.Expr e ->
        let (_, eta') = eval eta e in
        eta'
      | S.Block ss ->
        let eta' = Frame.push eta in
        begin
          match exec_many eta' ss with
          | Return v -> Return v
          | eta'' -> Frame.pop eta''
        end
      | S.If(e, s0, s1) ->
        let (v, eta') = eval eta e in
        begin
          match v with
          | Value.V_Bool true -> exec_one eta' s0
          | Value.V_Bool false -> exec_one eta' s1
          | _ -> raise @@ TypeError (
                   "Conditional test not a boolean value:  " ^ Value.to_string v
                 )
        end
      | S.While(e, body) ->
        (* dowhile η = η', where while e do body ├ η → η'.
         *)
        let rec dowhile (eta : Frame.t) : Frame.t =
          let (v, eta') = eval eta e in
          match v with
          | Value.V_Bool false -> eta'
          | Value.V_Bool true ->
            begin
              match exec_one eta' body with
              | Frame.Return v -> Frame.Return v
              | eta'' -> dowhile eta''
            end
          | _ -> raise @@ TypeError (
                   "While test not a boolean value:  " ^ Value.to_string v
                 )
        in
        dowhile eta
      | S.Return (Some e) ->
        let (v, _) = eval eta e in
        Frame.Return v
      | S.Return None ->
        Frame.Return Value.V_None

  (* exec_many η₀ [s_0,...,s_{n-1}] = η',
   *   if s_0 ├ η₀ → η₁
   *      s_1 ├ η₁ → η₂
   *      ...
   *      s_{n-1} ├ η_{n-1} → η'
   *      and η_i is not a return frame for any i;
   * exec_many η₀ [s_0,...,s_{n-1}] = η',
   *   if s_0 ├ η₀ → η₁
   *      s_1 ├ η₁ → η₂
   *      ...
   *      s_{j-1} ├ η_{j-1} → η'
   *      and η_i is not a return frame for any i<j and η' is a return
   *      frame.
   *)
  and exec_many (eta : Frame.t) (ss : Ast.Stm.t list) : Frame.t =
    match ss with
        | [] -> eta
        | s :: ss ->
          begin
            match exec_one eta s with
            | Frame.Return v -> Frame.Return v
            | eta' -> exec_many eta' ss
          end

  in
    let _ = eval Frame.base (E.Call ("main", [])) in
    ()

