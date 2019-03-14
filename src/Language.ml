(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let bool_of_int intValue = intValue != 0

    let int_of_bool boolValue = if boolValue then 1 else 0

    let apply_operation op left right = match op with
      | "+" -> (+) left right
      | "-" -> (-) left right
      | "*" -> ( * ) left right
      | "/" -> (/) left right
      | "%" -> (mod) left right
      | "!!" -> int_of_bool ((||) (bool_of_int left) (bool_of_int right))
      | "&&" -> int_of_bool ((&&) (bool_of_int left) (bool_of_int right))
      | "==" -> int_of_bool ((==) left right)
      | "!=" -> int_of_bool ((!=) left right)
      | "<=" -> int_of_bool ((<=) left right)
      | "<" -> int_of_bool ((<) left right)
      | ">=" -> int_of_bool ((>=) left right)
      | ">" -> int_of_bool ((>) left right)
      | _ -> failwith "Unknown operation"

    (* Expression evaluator
          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval state expr = match expr with
      | Const value -> value
      | Var name -> state name 
      | Binop (op, left, right) -> apply_operation op (eval state left) (eval state right)

    let createBinopParsePair op = ostap(- $(op)), fun left right -> Binop (op, left, right)

    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      expr: 
        !(Ostap.Util.expr
          (fun parsed -> parsed)
          (Array.map (fun (assoc, operations) -> assoc, List.map createBinopParsePair operations)
            [|
              `Lefta, ["!!"];
              `Lefta, ["&&"];
              `Nona,  ["<="; "<"; ">="; ">"; "=="; "!="];
              `Lefta, ["+"; "-"];
              `Lefta, ["*"; "/"; "%"];
            |]
          )
          primary
        );

      primary: name:IDENT {Var name} | value:DECIMAL {Const value} | -"(" expr -")"
    )

end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config statement = match (config, statement) with
    | ((state, value::inp, out), Read name) -> (Expr.update name value state, inp, out)
    | ((state, inp, out), Write expr) -> (state, inp, out @ [(Expr.eval state expr)])
    | ((state, inp, out), Assign (name, expr)) -> ((Expr.update name (Expr.eval state expr) state), inp, out)
    | (config, Seq (s1, s2)) -> eval (eval config s1) s2
    | _ -> failwith "Unknown operation"

  (* Statement parser *)
  ostap (
    parse: st:statement ";" rest:parse { Seq (st, rest) } | statement;
    statement: 
      "read" "(" name:IDENT ")" { Read name } 
      | "write" "(" expr:!(Expr.expr) ")" { Write expr } 
      | name:IDENT ":=" expr:!(Expr.expr) { Assign (name, expr) }
  )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
