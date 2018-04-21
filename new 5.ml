
(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
(*let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = failwith "Not implemented"*)

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| instruction :: rest_program ->
   match instruction with
      | BINOP op ->
        let y::x::tl_stack = stack
        in eval env (cstack, (Expr.to_func op x y) :: tl_stack, c) rest_program
      | READ     -> let z::i'        = i     in eval env (cstack, z::stack, (st, i', o)) rest_program
      | WRITE    -> let z::tl_stack    = stack in eval env (cstack, tl_stack, (st, i, o @ [z])) rest_program
      | CONST i  -> eval env (cstack, i::stack, c) rest_program
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) rest_program
      | ST x     -> let z::tl_stack    = stack in eval env (cstack, tl_stack, (State.update x z st, i, o)) rest_program
      | LABEL _ -> eval env conf rest_program
      | JMP label -> eval env conf (env#labeled label)
      | CJMP (condition, label) ->
        let x :: tl_stack = stack in
        eval env (cstack, tl_stack, c) (if (condition = "nz" && x != 0 || condition = "z" && x = 0)
                                        then (env#labeled label) else rest_program)
      | CALL f_name -> eval env ((rest_program, st)::cstack, stack, c) (env#labeled f_name)
      | BEGIN (args, local_vars) ->
        let current_state = State.enter st (args @ local_vars) in
        let (res_state, res_stack) = fold_right (fun arg (st, v::tl_stack) -> (State.update arg v st, tl_stack)) args (current_state, stack) in
        eval env (cstack, res_stack, (res_state, i, o)) rest_program
      | END ->
        match cstack with
        | [] -> conf
        | (stmts, s) :: tl_cstack -> eval env (tl_cstack, stack, (State.leave st s, i, o)) stmts

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let labels =
  object
    val mutable count = 0
    method generate =
        count <- count + 1;
        "label_" ^ string_of_int count
    end

let rec compile_expr expr =
    match expr with
    | Expr.Const c -> [CONST c]
    | Expr.Var v -> [LD v]
    | Expr.Binop (op, expr1, expr2) -> (compile_expr expr1) @ (compile_expr expr2) @ [BINOP op]
    | Expr.Call (f_name, args) -> concat (map compile_expr args) @ [CALL f_name]

let rec compile_statements stmts =
    match stmts with
    | Stmt.Read name -> [READ;ST name]
    | Stmt.Write expr -> compile_expr expr @ [WRITE]
    | Stmt.Assign (name, expr) -> compile_expr expr @ [ST name]
    | Stmt.Seq (stmt1, stmt2) -> compile_statements stmt1 @ compile_statements stmt2
    | Stmt.Skip -> []
    | Stmt.If (cond, th, els) ->
      let else_start_point = labels#generate in
      let endif_point = labels#generate in
      (compile_expr cond) @ [CJMP ("z", else_start_point)] @ (compile_statements th)@ [JMP endif_point; LABEL else_start_point] @ (compile_statements els) @ [LABEL endif_point]
    | Stmt.While (cond, body) ->
      let start_point = labels#generate in
      let end_point = labels#generate in
      [LABEL start_point] @ (compile_expr cond) @ [CJMP ("z", end_point)] @ (compile_statements body) @ [JMP start_point; LABEL end_point]
    | Stmt.Repeat (body, cond) ->
      let start_point = labels#generate in
      [LABEL start_point] @ (compile_statements body) @ (compile_expr cond) @ [CJMP ("z", start_point)]
    | Stmt.Call (f_name, args) -> concat (map compile_expr args) @ [CALL f_name]
    | Stmt.Return maybe_val -> match maybe_val with Some v -> (compile_expr v) @ [END] | _ -> [END]

let compile_definition (f_name, (args, local_vars, body)) = [LABEL f_name; BEGIN (args, local_vars)] @ (compile_statements body) @ [END]

let rec compile (defs, program) =
  [LABEL "main"] @ (compile_statements program) @ [END] @ (concat (map compile_definition defs))
