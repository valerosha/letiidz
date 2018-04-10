open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         

let rec eval env conf prog = 
	match prog with
	| instr::p -> (
		match conf, instr with
		| (cstack, y::x::stack, stmt_conf), BINOP operation -> 
			let value = Expr.binop operation x y in
			eval env (cstack, value::stack, stmt_conf) p
		| (cstack, stack, stmt_conf), CONST value ->
			eval env (cstack, value::stack, stmt_conf) p
		| (cstack, stack, (st, z::input, output)), READ ->
			eval env (cstack, z::stack, (st, input, output)) p
		| (cstack, z::stack, (st, input, output)), WRITE ->
			eval env (cstack, stack, (st, input, output @ [z])) p
		| (cstack, stack, (st, input, output)), LD variable ->
			let value = 
				State.eval st variable in
			eval env (cstack, value::stack, (st, input, output)) p
		| (cstack, z::stack, (st, input, output)), ST variable ->
			let st' =
				State.update variable z st in
			eval env (cstack, stack, (st', input, output)) p
		| conf, LABEL label ->
			 eval env conf p
		| conf, JMP label ->
			eval env conf (env#labeled label)
		| (cstack, z::stack, stmt_conf), CJMP (suf, label) -> (
			match suf with
			| "z" -> 
				if z == 0 then eval env (cstack, stack, stmt_conf) (env#labeled label)
				else eval env (cstack, stack, stmt_conf) p
			| "nz" -> 
				if z <> 0 then eval env (cstack, stack, stmt_conf) (env#labeled label)
				else eval env (cstack, stack, stmt_conf) p
			| _ -> failwith("Undefined suffix!")
		)
		| (cstack, stack, (st, input, output)), CALL name ->
			eval env ((p, st)::cstack, stack,(st, input, output)) (env#labeled name)
		| (cstack, stack, (st, input, output)), BEGIN (args, locals) ->
			let rec associate st args stack = 
				match args, stack with
				| arg::args', z::stack' -> 
					let st', stack'' = associate st args' stack' in
					(State.update arg z st', stack'')
				| [], stack' -> (st, stack') in
			let st', stack' = associate (State.enter st (args @ locals)) args stack in
			eval env (cstack, stack',(st',input, output)) p
		| (cstack, stack, (st, input, output)), END -> (
			match cstack with
			| (p', st')::cstack' -> 
				eval env (cstack', stack, (State.leave st' st, input, output)) p'
			| [] -> conf
		)

	)
	| [] -> conf


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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)


let rec compileExpr expr = 
	match expr with
	| Expr.Const value -> [CONST value]
	| Expr.Var variable -> [LD variable]
	| Expr.Binop (operation, left, right) ->
		compileExpr left @ compileExpr right @ [BINOP operation]

let rec compileControl stmt env = 
		match stmt with
	| Stmt.Assign (variable, expr) -> compileExpr expr @ [ST variable], env
	| Stmt.Read variable -> [READ; ST variable], env
	| Stmt.Write expr ->	compileExpr expr @ [WRITE], env
	| Stmt.Seq (left_stmt, right_stmt) -> 
		let left, env = compileControl left_stmt env in
		let right, env = compileControl right_stmt env in
		left @ right, env
	| Stmt.Skip -> [], env
	| Stmt.If (expr, th, el) ->
		let label_else, env = env#generate in 
		let label_fi, env = env#generate in
		let th_compile, env = compileControl th env in
		let el_compile, env = compileControl el env in
		compileExpr expr @ [CJMP ("z", label_else)] @ th_compile @ [JMP label_fi; LABEL label_else] @ el_compile @ [LABEL label_fi], env
	| Stmt.While (expr, while_stmt) ->
		let label_check, env = env#generate in
		let label_loop, env = env#generate in
		let while_body, env = compileControl while_stmt env in
		[JMP label_check; LABEL label_loop] @ while_body @ [LABEL label_check] @ compileExpr expr @ [CJMP ("nz", label_loop)], env
	| Stmt.Repeat (expr, repeat_stmt) ->
		let label_loop, env = env#generate in
		let repeat_body, env = compileControl repeat_stmt env in
		[LABEL label_loop] @ repeat_body @ compileExpr expr @ [CJMP ("z", label_loop)], env
	| Stmt.Call (name, args) ->
		List.concat (List.map compileExpr args) @ [CALL name], env

let compile (defs, stmt) = 
	let env = 
		object
    		val count_label = 0
    		method generate = "LABEL_" ^ string_of_int count_label, {< count_label = count_label + 1 >}
  		end in
	let prog, env = compileControl stmt env in
	let rec compile_defs env defs =
		match defs with
		 | (name, (args, locals, body))::defs' ->
		 		let body_defs, env = compile_defs env defs' in
		 		let compile_body, env = compileControl body env in 
				[LABEL name; BEGIN (args, locals)] @ compile_body @ [END] @ body_defs, env
		 | [] -> [], env  in
	let cdefs, _  = compile_defs env defs in 
	prog @ [END] @ cdefs
