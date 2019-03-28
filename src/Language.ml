(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
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
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (state, inp, out) statement = 
      let config = (state, inp, out) in
      match statement with
        | Read name -> 
          let value = List.hd inp in
          let rest = List.tl inp in
          State.update name value state, rest, out
        | Write expr -> state, inp, out @ [(Expr.eval state expr)]
        | Assign (name, expr) -> (State.update name (Expr.eval state expr) state), inp, out
        | Seq (s1, s2) -> eval env (eval env config s1) s2
        | Skip -> config
        | If (cond, st1, st2) ->
          if (Expr.eval state cond) != 0 
            then (eval env config st1)
            else (eval env config st2)
        | While (cond, st) ->
          if (Expr.eval state cond) != 0
            then let updated = (eval env config st) in eval env updated statement
            else config
        | Repeat (st, cond) ->
          let updated = (eval env config st) in
          let (u_state, u_inp, u_out) = updated in 
          if (Expr.eval u_state cond) != 0
            then updated
            else eval env updated statement
        | Call (name, args) ->
          let (arg_names, local_names, body) = env#definition name in
          let arg_values = List.map (Expr.eval state) args in
          let arg_pairs =  List.combine arg_names arg_values in
          let fun_state = State.push_scope state (arg_names @ local_names) in
          let fun_env_w_args = List.fold_left (fun s (name, value) -> State.update name value s) fun_state arg_pairs in
          let updated_fun_state, updated_inp, updated_out = eval env (fun_env_w_args, inp, out) body in
          State.drop_scope updated_fun_state state, updated_inp, updated_out
        | _ -> failwith "Unknown statement"
    

    (* Statement parser *)
    ostap (
      parse: st:statement ";" rest:parse { Seq (st, rest) } | statement;
      statement: 
        "read" "(" name:IDENT ")" { Read name } 
        | "write" "(" expr:!(Expr.parse) ")" { Write expr } 
        | name:IDENT ":=" expr:!(Expr.parse) { Assign (name, expr) }
        | "skip" { Skip }
        | "if" cond:!(Expr.parse) "then" st1:parse st2:eliffi { If (cond, st1, st2) }
        | "while" cond:!(Expr.parse) "do" st:parse "od" { While (cond, st) }
        | "repeat" st:parse "until" cond:!(Expr.parse) { Repeat (st, cond) }
        | "for" init:parse "," cond:!(Expr.parse) "," upd:parse "do" st:parse "od" { Seq (init, While (cond, Seq (st, upd))) }
        | name:IDENT "(" args:(!(Expr.parse))* ")" { Call (name, args) };

      eliffi:
        "fi" { Skip }
        | "else" st:parse "fi" { st }
        | "elif" cond:!(Expr.parse) "then" st1:parse st2:eliffi { If (cond, st1, st2) }
    ) 
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      parse: 
        "fun" name:IDENT "(" args:(IDENT)* ")" 
        local:(%"local" (IDENT)*)? "{" 
          body:!(Stmt.parse)
        "}" {
          let local = match local with 
            | Some x -> x
            | _ -> []
          in
          name, (args, local, body)
        } 
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
