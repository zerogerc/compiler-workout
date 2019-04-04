(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                    
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

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
      | Const n -> (st, i, o, Some n)
      | Var   x -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y) -> 
        let (st1, i1, o1, Some res1) = eval env conf x in
        let (st2, i2, o2, Some res2) = eval env (st1, i1, o1, None) y in
        (st2, i2, o2, Some (to_func op res1 res2))
      | Call (name, args) -> 
        let args_fold = (fun (st, i, o, arg_values) arg -> 
          let (upd_s, upd_i, upd_o, Some value) = eval env (st, i, o, None) arg in 
          (upd_s, upd_i, upd_o, arg_values @ [value])
        ) in
        let upd_st, upd_i, upd_o, arg_values = List.fold_left args_fold (st, i, o, []) args in
        env#definition env name arg_values (upd_st, upd_i, upd_o, None)
         
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
          | -"(" parse -")"
          | name:IDENT "(" args:!(Util.list0 parse) ")" { Call (name, args) }
          | name:IDENT {Var name}
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let combine_continuation k stmt =
        match k with
          | Skip -> stmt
          | _ -> Seq (stmt, k) 
      in
      match stmt with
      | Read name -> 
        let value = List.hd i in
        let rest = List.tl i in
        eval env (State.update name value st, rest, o, None ) Skip k
      | Write expr ->
        let (u_st, u_i, u_o, Some value) = Expr.eval env conf expr in 
        eval env (u_st, u_i, u_o @ [value], None) Skip k
      | Assign (name, expr) -> 
        let (u_st, u_i, u_o, Some value) = Expr.eval env conf expr in
        eval env (State.update name value u_st, u_i, u_o, Some value) Skip k
      | Seq (s1, s2) -> eval env conf (combine_continuation k s2) s1
      | Skip -> (match k with
        | Skip -> conf
        | _ -> eval env conf Skip k)
      | If (cond, st1, st2) ->
        let (u_st, u_i, u_o, Some cond_value) = Expr.eval env conf cond in
        if cond_value != 0 
          then eval env (u_st, u_i, u_o, None) k st1
          else eval env (u_st, u_i, u_o, None) k st2
      | While (cond, body) ->
        let (u_st, u_i, u_o, Some cond_value) = Expr.eval env conf cond in
        if cond_value != 0
          then eval env (u_st, u_i, u_o, None) (combine_continuation k stmt) body 
          else eval env (u_st, u_i, u_o, None) Skip k
      | Repeat (body, cond) ->
        eval env conf (combine_continuation k (While (Expr.Binop ("==", cond, Expr.Const 0), body))) body
      | Call (name, args) ->
        eval env (Expr.eval env conf (Expr.Call (name, args))) Skip k
      | Return res -> (match res with
        | Some expr -> Expr.eval env conf expr 
        | _ -> (st, i, o, None))
         
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
        | name:IDENT "(" args:!(Util.list0 Expr.parse) ")" { Call (name, args) }
        | "return" expr:!(Expr.parse)? { Return expr };

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
      arg: IDENT;
      parse: 
        "fun" name:IDENT "(" args:!(Util.list0 arg) ")" 
        local:(%"local" !(Util.list arg))? "{" 
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
