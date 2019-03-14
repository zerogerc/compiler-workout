open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

let execute_instruction config instruction = match config, instruction with
  | (y::x::stack, s_config), BINOP op -> 
    let expr = Expr.Binop (op, Expr.Const x, Expr.Const y) in 
    let result = Expr.eval Expr.empty expr in 
    result::stack, s_config
  | (stack, s_config), CONST value -> value::stack, s_config
  | (stack, (state, in_value::inp, out)), READ -> in_value::stack, (state, inp, out)
  | (s_value::stack, (state, inp, out)), WRITE -> stack, (state, inp, out @ [s_value])
  | (stack, (state, inp, out)), LD name -> (state name)::stack, (state, inp, out)
  | (s_value::stack, (state, inp, out)), ST name -> stack, (Expr.update name s_value state, inp, out)
  | _ -> failwith "Unknown instruction"

(* Stack machine interpreter
     val eval : config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         
 let rec eval config program = match config, program with
  | config, [] -> config
  | config, instruction::rest -> eval (execute_instruction config instruction) rest

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Language.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]