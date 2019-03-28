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

let execute_instruction config instruction = 
  let stack, (state, inp, out) = config in
  let stmt_config = (state, inp, out) in
  match instruction with
    | BINOP op ->
        let y::x::rest = stack in 
        let expr = Expr.Binop (op, Expr.Const x, Expr.Const y) in 
        let result = Expr.eval state expr in 
        result::rest, stmt_config
    | CONST value -> value::stack, stmt_config
    | READ -> (List.hd inp)::stack, (state, (List.tl inp), out)
    | WRITE -> (List.tl stack), (state, inp, out @ [List.hd stack])
    | LD name -> (State.eval state name)::stack, (state, inp, out)
    | ST name -> (List.tl stack), (State.update name (List.hd stack) state, inp, out)
    | _ -> failwith "Unknown instruction"

(* Stack machine interpreter

    val eval : env -> config -> prg -> config

  Takes an environment, a configuration and a program, and returns a configuration as a result. The
  environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env config program = 
  let (control_stack, stack, (state, i, o)) = config in
    match program with
    [] -> config
    | LABEL l :: rest -> eval env config rest
    | JMP l :: _ -> eval env config (env#labeled l)
    | CJMP (z, l) :: rest ->
        if (z = "z" && (List.hd stack) == 0 || z = "nz" && (List.hd stack) != 0)
          then eval env (control_stack, List.tl stack, (state, i, o)) (env#labeled l) 
          else eval env (control_stack, List.tl stack, (state, i, o)) rest
    | BEGIN (arg_names, local_names) :: rest ->
      let fun_state = State.push_scope state (arg_names @ local_names) in
      let updated_state, updated_stack = 
        List.fold_left 
          (fun (s, value::stack_tail) name -> (State.update name value s, stack_tail))
          (fun_state, stack)
          arg_names
      in
      eval env (control_stack, updated_stack, (updated_state, i, o)) rest
    | END :: _ -> (match control_stack with
      | (before_prg, before_state)::cs_rest -> 
        eval env (cs_rest, stack, (State.drop_scope state before_state, i, o)) before_prg
      | _ -> config
    )
    | CALL name :: rest -> 
      let jmp_prg = env#labeled name in
      eval env ((rest, state)::control_stack, stack, (state, i, o)) jmp_prg
    | instruction::rest ->
      let updated_stack, updated_config = execute_instruction (stack, (state, i, o)) instruction in
      eval env (control_stack, updated_stack, updated_config) rest

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

let label_generator =
  object (self)
    val mutable next = 0

    method generate = 
      next <- next + 1;
      ".label" ^ (string_of_int next)
  end
  
(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile_block stmt end_label =
  let rec expr = function
    | Expr.Var x -> [LD x]
    | Expr.Const n -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op] in
  match stmt with
    | Stmt.Seq (s1, s2) -> 
      let l_end1 = label_generator#generate in
      let prg1, used1 = compile_block s1 l_end1 in
      let prg2, used2 = compile_block s2 end_label in
      prg1 @ (if used1 then [LABEL l_end1] else []) @ prg2, used2
    | Stmt.Read x -> [READ; ST x], false
    | Stmt.Write e -> expr e @ [WRITE], false
    | Stmt.Assign (x, e) -> expr e @ [ST x], false
    | Stmt.Skip -> [], false
    | Stmt.If (e, s1, s2) ->
      let l_else = label_generator#generate in
      let if_prg, used1 = compile_block s1 end_label in
      let else_prg, used2 = compile_block s2 end_label in
      expr e @ [CJMP ("z", l_else)] @ if_prg @ [JMP end_label] @ [LABEL l_else] @ else_prg @ [JMP end_label], true
    | Stmt.While (e, s) ->
      let l_cond = label_generator#generate in
      let l_loop = label_generator#generate in
      let loop_prg, _ = compile_block s l_cond in
      [JMP l_cond; LABEL l_loop] @ loop_prg @ [LABEL l_cond] @ expr e @ [CJMP ("nz", l_loop)], false
    | Stmt.Repeat (s, e) ->
        let l_repeat = label_generator#generate in
        let repeat_prg = compile_stmt s in
        [LABEL l_repeat] @ repeat_prg @ expr e @ [CJMP ("z", l_repeat)], false
    | Stmt.Call (name, args) ->
      List.concat (List.map expr (List.rev args)) @ [CALL name], false
and compile_stmt stmt =
  let end_label = label_generator#generate in
  let prg, used = compile_block stmt end_label in
  prg @ (if used then [LABEL end_label] else []) 
and compile_defs defs =
  List.fold_left 
  (fun prev (name, (args, locals, body)) -> 
    let compiled_body = compile_stmt body in 
    prev @ [LABEL name] @ [BEGIN (args, locals)] @ compiled_body @ [END]
  )
  []
  defs
and compile (defs, stmt) = 
  let compiled_stmt = compile_stmt stmt in
  let compiled_defs = compile_defs defs in
  compiled_stmt @ [END] @ compiled_defs