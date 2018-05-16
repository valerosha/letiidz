open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env cfg prg =
  match prg with
  | [] -> cfg
  | instr::prg_tail ->
    let (cstack, stack, config) = cfg in
    let (state, input, output) = config in
    match instr with
    | BINOP op ->
      let (x::y::stack_tail) = stack in
      eval env (cstack,  (Value.of_int (Expr.binop op (Value.to_int y) (Value.to_int x))) :: stack_tail, config) prg_tail
    | CONST c -> eval env (cstack, (Value.of_int c)::stack, config) prg_tail
    | STRING s -> eval env (cstack, (Value.of_string s)::stack, config) prg_tail
    | LD x -> eval env (cstack, (State.eval state x)::stack, config) prg_tail
    | ST x -> 
      let (s::stack_tail) = stack in
      eval env (cstack, stack_tail, ((State.update x s state), input, output)) prg_tail
    | STA (x, n) -> let v::ind, stack' = split (n + 1) stack in eval env (cstack, stack', (Language.Stmt.update state x v (List.rev ind), input, output)) prg_tail
    | LABEL _ -> eval env cfg prg_tail
    | JMP label -> eval env cfg (env#labeled label)
    | CJMP (cond, label)  -> 
      let (s::stack_tail) = stack in
      let x = match cond with
      | "nz" -> Value.to_int s <> 0
      | "z" -> Value.to_int s = 0 
      in eval env (cstack, stack_tail, config) (if (x) then (env#labeled label) else prg_tail)
    | CALL (f, n, p) -> if env#is_label f then eval env ((prg_tail, state)::cstack, stack, config) (env#labeled f) else eval env (env#builtin cfg f n p) prg_tail
    | BEGIN (_, args, xs) ->
      let rec get_args state = function
        | a::args, z::stack -> let state', stack' = get_args state (args, stack)
        in State.update a z state', stack'
        | [], stack -> state, stack
      in let state', stack' = get_args (State.enter state @@ args @ xs) (args, stack)
      in eval env (cstack, stack', (state', input, output)) prg_tail
    | END | RET _ ->
      match cstack with
      | (prog, s)::cstack' ->
        eval env (cstack', stack, (State.leave state s, input, output)) prog
      | [] -> cfg

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

let rec compile_expr expr = 
  match expr with
  | Expr.Const c -> [CONST c]
  | Expr.Var x -> [LD x]
  | Expr.String s -> [STRING s]
  | Expr.Array arr -> List.flatten (List.map compile_expr arr) @ [CALL ("$array", List.length arr, false)]
  | Expr.Elem (arr, i) -> compile_expr arr @ compile_expr i @ [CALL ("$elem", 2, false)]
  | Expr.Length t -> compile_expr t @ [CALL ("$length", 1, false)]
  | Expr.Binop (op, left_expr, right_expr) -> compile_expr left_expr @ compile_expr right_expr @ [BINOP op]
  | Expr.Call (f, exprs) -> List.fold_left (fun ac e -> compile_expr e @ ac) [] exprs @ [CALL ("L" ^ f, List.length exprs, false)]

let env = object 
  val mutable id = 0
  method next_label = 
    id <- (id + 1);
    "L" ^ string_of_int id
end

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, st) = 
  let rec compile' st =
    match st with
    | Stmt.Assign (x, [], e) -> compile_expr e @ [ST x]
    | Stmt.Assign (x, is, e) -> List.flatten (List.map compile_expr (is @ [e])) @ [STA (x, List.length is)]
    | Stmt.Seq (left_st, right_st) -> (compile' left_st) @ (compile' right_st)
    | Stmt.Skip -> []
    | Stmt.If (e, s1, s2) ->
      let else_label = env#next_label in
      let end_label = env#next_label in
      let current_case = compile' s1 in
      let last_case = compile' s2 in
      (compile_expr e @ [CJMP ("z", else_label)] @ current_case @ [JMP end_label] @ [LABEL else_label] @ last_case @ [LABEL end_label])
    | Stmt.While (e, s) ->
      let end_label = env#next_label in
      let loop_label = env#next_label in
      let body = compile' s in
      ([JMP end_label] @ [LABEL loop_label] @ body @ [LABEL end_label] @ compile_expr e @ [CJMP ("nz", loop_label)])
    | Stmt.Repeat (e, s) ->
      let loop_label = env#next_label in
      let body = compile' s in
      ([LABEL loop_label] @ body @ compile_expr e @ [CJMP ("z", loop_label)])
    | Stmt.Return e -> (
      match e with
      | None -> [RET false]
      | Some expr -> compile_expr expr @ [RET true]
    )
    | Stmt.Call (name, args) -> 
      List.concat (List.map compile_expr args) @ [CALL ("L" ^ name, List.length args, true)] in
      let compile_def (name, (args, locals, body)) = [LABEL ("L" ^ name); BEGIN (name, args, locals)] @ compile' body @ [END] in
      (compile' st @ [END] @ List.concat (List.map compile_def defs))
