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
  type t = 
    | V_Undefined
    | V_None
    | V_Int of int
    | V_Bool of bool
    | V_Str of string
    [@@deriving show]

  (* to_string v = a string representation of v (more human-readable than
   * `show`.
   *)
  let to_string (v : t) : string =
    match v with
    | V_Undefined -> "?"
    | V_None -> "None"
    | V_Int n -> Int.to_string n
    | V_Bool b -> Bool.to_string b
    | V_Str s -> s
end

module Frame = struct

  (* The type of environments.
   *)
  type env = Value.t IdentMap.t

  (* A frame is either a list of environments or a return frame with a
   * value.
   *)
  type t = Envs of env list | Return of Value.t

  (* A base environment frame.
   *)
  let base : t = Envs [IdentMap.empty]

  (* to_string η is a string representation of η.
   *)
  let to_string (eta : t) : string =
    match eta with
    | Return v -> Value.to_string v
    | Envs sigmas ->
      sigmas |> List.map IdentMap.to_list
             |> List.map (
                  fun l ->
                    String.concat ", " (
                      List.map (fun (id, v) -> id ^ ": " ^ Value.to_string v) l
                    )
                )
             |> String.concat "; "

  (* lookup η x = v, where η = Envs [σ_0,...,σ_{n-1}], σ_i(x) = v, and
   * x is not in the domain of any σ_j for j<i.
   *
   * Raises Failure if η is a return frame.
   * Raises UnboundVariable if x not in dom σ_i for any i.
   *)
  let lookup (eta : t) (x : Ast.Id.t) : Value.t =
    (* lookup' [σ_0,...,σ_{n-1}] = v, where σ_i(x) = v and x is not in the
     * domain of any σ_j for j<i.
     *
     * Raises Failure if η is a return frame.
     *)
    let rec lookup' (sigmas : env list) : Value.t =
        match sigmas with
        | [] -> raise @@ UnboundVariable x
        | sigma :: sigmas ->
          try IdentMap.find x sigma with
          | Not_found -> lookup' sigmas
    in match eta with
    | Envs eta -> lookup' eta
    | Return _ -> impossible "Bad frame"

  (* set η  x v = Envs [σ_0,...,σ_i[x→v],...], 
   *   where η = Envs [σ_0,...,σ_{n-1}], x ∈ dom(σ_i) and x not in dom(σ_j)
   *   for j < i.
   *
   * Raises Failure if η is a return frame.
   * Raises UnboundVariable if x not in dom σ_i for any i.
   *)
  let set (eta : t) (x : Ast.Id.t) (v : Value.t) : t =
    (* set' [σ_0,...,σ_{n-1}] = [σ_0,...,σ_i[x→v],...], x ∈ dom(σ_i) and x
     * not in dom(σ_j) for j < i.
     *)
    let rec set' (sigmas : env list) : env list =
      match sigmas with
      | [] -> raise @@ UnboundVariable x
      | sigma :: sigmas ->
        if IdentMap.mem x sigma
        then IdentMap.add x v sigma :: sigmas
        else sigma :: set' sigmas
    in match eta with
    | Envs sigmas -> Envs (set' sigmas)
    | Return _ -> impossible "Bad frame"


  (* declare η x v = Envs [σ₀[x→v],σ₁,...], where η = Envs [σ₀,σ₁,...].
   *
   * Raises Failure if η a return frame and or Envs [].
   * Raises MultipleDeclaration if x ∈ dom σ₀.
   *)
  let declare (eta : t) (x : Ast.Id.t) (v : Value.t) : t =
    match eta with
    | Envs [] -> impossible "declaration with empty frame."
    | Envs (sigma :: sigmas) ->
      if IdentMap.mem x sigma
      then raise @@ MultipleDeclaration x
      else Envs (IdentMap.add x v sigma :: sigmas)
    | Return _ -> impossible "declaration with Return frame."

  (* push (Envs σs) = Envs ({} :: σs).
   * push (Return _): raises Failure.
   *)
  let push (eta : t) : t =
    match eta with
    | Envs sigmas -> Envs (IdentMap.empty :: sigmas)
    | Return _ -> impossible "Bad frame"

  (* pop (Envs σ :: σs) = Envs (σs).
   * pop (Envs []): raises Failure
   * pop (Return _):  raises Failure
   *)
  let pop (eta : t) : t =
    match eta with
    | Envs [] -> impossible "Frame.pop on empty frame"
    | Envs (_ :: sigmas) -> Envs sigmas
    | Return _ -> impossible "Bad frame"

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
let binop (op : E.binop) (v : Value.t) (v' : Value.t) : Value.t =
  match (op, v, v') with
  | (E.Plus, Value.V_Int n, Value.V_Int n') -> Value.V_Int (n + n')
  | (E.Minus, Value.V_Int n, Value.V_Int n') -> Value.V_Int (n - n')
  | (E.Times, Value.V_Int n, Value.V_Int n') -> Value.V_Int (n * n')
  | (E.Div, Value.V_Int n, Value.V_Int n') -> Value.V_Int (n / n')
  | (E.Mod, Value.V_Int n, Value.V_Int n') -> Value.V_Int (n mod n')
  | (E.And, Value.V_Bool b, Value.V_Bool b') -> Value.V_Bool (b && b')
  | (E.Or, Value.V_Bool b, Value.V_Bool b') -> Value.V_Bool (b || b')
  | (E.Eq, v, v') -> Value.V_Bool (v = v')
  | (E.Ne, v, v') -> Value.V_Bool (v <> v')
  | (E.Lt, Value.V_Int n, Value.V_Int n') -> Value.V_Bool (n < n')
  | (E.Le, Value.V_Int n, Value.V_Int n') -> Value.V_Bool (n <= n')
  | (E.Gt, Value.V_Int n, Value.V_Int n') -> Value.V_Bool (n > n')
  | (E.Ge, Value.V_Int n, Value.V_Int n') -> Value.V_Bool (n >= n')
  | _ -> raise @@
         TypeError (
           Printf.sprintf "Bad operand types: %s %s %s"
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

