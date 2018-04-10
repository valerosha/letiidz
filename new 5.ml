pen GT       
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
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let rec eval env ((cstack, stack, ((st, i, o, r) as c)) as conf) prg =
	match prg with
	| [] -> conf
	| inst :: tail -> 
	  let cfg, next = 
		 (match inst with 
		  | BINOP binop -> 
				(match stack with 
					  y :: x :: st_end -> (cstack, (Expr.calc binop x y) :: st_end, c), tail
					| _ -> failwith "Not enough arguments for binary operation")
		  | CONST n -> (cstack, n :: stack, c), tail
		  | READ -> let num = List.hd i in (cstack , num :: stack, (st, List.tl i, o, None)), tail
		  | WRITE -> let num = List.hd stack in (cstack, List.tl stack, (st, i, o @ [num], None)), tail
		  | LD x -> (cstack, (State.eval st x) :: stack, c), tail
		  | ST x -> let num = List.hd stack in (cstack, List.tl stack, (State.update x num st, i, o, None)), tail
		  | LABEL _ -> conf, tail
		  | JMP l -> conf, (env#labeled l)
		  | CJMP (op, l) ->
				let cmp = List.hd stack in
				let ret = if (op = "z" && cmp = 0) || (op = "nz" && cmp <> 0) then (env#labeled l) else tail in
				(cstack, List.tl stack, c), ret
		  | BEGIN (params, locals) ->
				let new_st = State.enter st (params @ locals) in
				let st', stack' = List.fold_left (fun (a_st, v :: a_stack) p -> State.update p v a_st, a_stack) (new_st, stack) params in
				(cstack, stack', (st', i, o, None)), tail
		  | END -> 
			   (match cstack with
				| [] -> conf, []
				| (prg', st') :: rest -> 
					let new_st = State.leave st st' in
					(rest, stack, (new_st, i, o, None)), prg')
		  | CALL proc -> ((tail, st) :: cstack, stack, c), (env#labeled proc)) in
	  eval env cfg next

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
  let (_, _, (_, _, o, _)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], None)) p in o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) =
	let label_creator =
		object
			val cur_val = 0
			method name x = "proc_" ^ x
			method get = "label_" ^ string_of_int cur_val, {< cur_val = cur_val + 1 >}
		end in
	let rec compile_expr lbl (expr : Language.Expr.t) = 
		(match expr with
		| Expr.Const n -> [CONST n]
		| Expr.Var x -> [LD x]
		| Expr.Binop (binop, x, y) -> compile_expr lbl x @ compile_expr lbl y @ [BINOP binop]
		| Expr.Call (proc, params) -> 
			let compiled_params = List.fold_right (fun expr lst -> lst @ (compile_expr lbl expr)) params [] in
			(compiled_params @ [CALL (lbl#name proc)])) in
	let rec compile_label lbl stmt = 
	   (match stmt with
		  Stmt.Read x -> lbl, [READ; ST x]
		| Stmt.Write expr -> lbl, (compile_expr lbl expr) @ [WRITE]
		| Stmt.Assign (x, expr) -> lbl, (compile_expr lbl expr) @ [ST x]
		| Stmt.Seq (stmt_left, stmt_right) ->
			let lbl, left = compile_label lbl stmt_left in
			let lbl, right = compile_label lbl stmt_right in
			lbl, left @ right
		| Stmt.Skip -> lbl, []
		| Stmt.If (cond, t, f) ->
			let flbl, lbl = lbl#get in
			let endlbl, lbl = lbl#get in
			let lbl, ift = compile_label lbl t in
			let lbl, iff = compile_label lbl f in
			let instr = 
				match f with
				| Skip -> [LABEL flbl]
				| _ -> [JMP endlbl; LABEL flbl] @ iff @ [LABEL endlbl] in
			lbl, (compile_expr lbl cond) @ [CJMP ("z", flbl)] @ ift @ instr
		| Stmt.While (cond, st) ->
			let initlbl, lbl = lbl#get in
			let endlbl, lbl = lbl#get in
			let lbl, body = compile_label lbl st in
			lbl, [JMP endlbl; LABEL initlbl] @ body @ [LABEL endlbl] @ (compile_expr lbl cond) @ [CJMP ("nz", initlbl)]
		| Stmt.Repeat (st, cond) ->
			let initlbl, lbl = lbl#get in
			let lbl, body = compile_label lbl st in
			lbl, [LABEL initlbl] @ body @ (compile_expr lbl cond) @ [CJMP ("z", initlbl)]
		| Stmt.Return expr -> 
			let ret =
			(match expr with
			| None -> []
			| Some e -> compile_expr lbl e) in
			lbl, ret @ [END]
		| Stmt.Call (proc, params) -> lbl, compile_expr lbl (Expr.Call (proc, params))) in
	let rec compile_def lbl procs =
		match procs with
		| [] -> lbl, []
		| (proc, (args, locals, body)) :: ps -> 
			let lbl, compiled_body = compile_label lbl body in
			let lbl, rest = compile_def lbl ps in
			lbl, [LABEL (lbl#name proc); BEGIN (args, locals)] @ compiled_body @ [END] @ rest in 
	let lbl, procs = compile_def label_creator defs in
	let _, code = compile_label lbl p
	in code @ [END] @ procs