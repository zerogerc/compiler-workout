open GT       
       
open Syntax

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

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                
 
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

let rec eval config program = match config, program with
  | config, [] -> config
  | config, instruction::rest -> eval (execute_instruction config instruction) rest

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile_expr expr = match expr with
  | Expr.Const value -> [CONST value]
  | Expr.Var name -> [LD name]
  | Expr.Binop (op, exp1, exp2) -> (compile_expr exp1) @ (compile_expr exp2) @ [BINOP op] 


let rec compile st = match st with
  | Stmt.Read name -> [READ; ST name]
  | Stmt.Write expr -> (compile_expr expr) @ [WRITE]
  | Stmt.Assign (name, expr) -> (compile_expr expr) @ [ST name]
  | Stmt.Seq (st1, st2) -> (compile st1) @ (compile st2)
