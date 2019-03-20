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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

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
    | LD name -> (state name)::stack, (state, inp, out)
    | ST name -> (List.tl stack), (Expr.update name (List.hd stack) state, inp, out)
    | _ -> failwith "Unknown instruction"


(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
(* let rec eval env conf prog = failwith "Not yet implemented" *)

let rec eval env config program = 
  let (stack, (s, i, o)) = config in
    match program with
    [] -> config
    | LABEL l::p -> eval env config p
    | JMP l::_ -> eval env config (env#labeled l)
    | CJMP (z, l) :: p ->
        if (z = "z" && (List.hd stack) == 0 || z = "nz" && (List.hd stack) != 0)
          then eval env (List.tl stack, (s, i, o)) (env#labeled l) 
          else eval env (List.tl stack, (s, i, o)) p
    | instruction::rest -> eval env (execute_instruction config instruction) rest

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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

let label_generator =
  object (self)
    val mutable next = 0

    method generate = 
      next <- next + 1;
      ".label" ^ (string_of_int next)
  end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var x -> [LD x]
  | Expr.Const n -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2) -> compile s1 @ compile s2
  | Stmt.Read x -> [READ; ST x]
  | Stmt.Write e -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
  | Stmt.Skip -> []
  | Stmt.If (e, s1, s2) ->
    let l_else = label_generator#generate in
    let l_end = label_generator#generate in
    expr e @ [CJMP ("z", l_else)] @ compile s1 @ [JMP l_end; LABEL l_else] @ compile s2 @ [LABEL l_end]
  | Stmt.While (e, s) ->
    let l_cond = label_generator#generate in
    let l_loop = label_generator#generate in
    [JMP l_cond; LABEL l_loop] @ compile s @ [LABEL l_cond] @ expr e @ [CJMP ("nz", l_loop)]
  | Stmt.Repeat (s, e) ->
      let l_repeat = label_generator#generate in
      [LABEL l_repeat] @ compile s @ expr e @ [CJMP ("z", l_repeat)] 