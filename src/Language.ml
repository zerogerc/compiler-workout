(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let list_init size f = 
    let rec list_init_rec i size f = if i < size then (f i) :: (list_init_rec (i + 1) size f) else [] in
    list_init_rec 0 size f

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
    
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

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                               
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
      | Const n -> (st, i, o, Some (Value.of_int n))
      | Array exprs -> 
        let (st, i, o, values) = eval_list env conf exprs in
        (st, i, o, Some (Value.of_array values))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Var name -> (st, i, o, Some (State.eval st name))
      | Binop (op, x, y) -> 
        let (st, i, o, Some res1) = eval env conf x in
        let (st, i, o, Some res2) = eval env (st, i, o, None) y in
        (st, i, o, Some (Value.of_int (to_func op (Value.to_int res1) (Value.to_int res2))))
      | Elem (arr_expr, idx_expr) ->
        let (st, i, o, Some idx) as conf = eval env conf idx_expr in
        let (st, i, o, Some arr) as conf = eval env conf arr_expr in
        let idx_value = Value.to_int idx in
        let value = match arr with
          | String s -> Value.of_int (Char.code s.[idx_value])
          | Array a -> List.nth a idx_value
          | _ -> failwith "Not an array type"
          in
        (st, i, o, Some value)
      | Length arr_expr -> 
        let (st, i, o, Some arr) as conf = eval env conf arr_expr in
        let arr_len = match arr with
          | String s -> Value.of_int (String.length s)
          | Array a -> Value.of_int (List.length a)
          | _ -> failwith "Not an array type" in
        (st, i, o, Some arr_len)
      | Call (name, args) ->
        let st, i, o, arg_values = eval_list env conf args in 
        env#definition env name arg_values (st, i, o, None)
      | _ -> failwith "Unknown expression type" 
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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
          arr_expr);

      arr_expr: e:primary elems:(-"[" !(parse) -"]")* length:(".length")? {
        let e = List.fold_left (fun e id -> Elem (e, id)) e elems in
        match length with | Some _ -> Length e | _ -> e
      };

      primary:
        n:DECIMAL { Const n }
        | c:CHAR { Const (Char.code c) }
        | str:STRING { String (String.sub str 1 (String.length str - 2)) }
        | -"(" parse -")"
        | name:IDENT "(" args:!(Util.list0 parse) ")" { Call (name, args) }
        | name:IDENT { Var name }
        | "[" exprs:!(Util.list0 parse) "]" { Array exprs }
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let combine_continuation k stmt =
        match k with
          | Skip -> stmt
          | _ -> Seq (stmt, k) 
      in
      match stmt with
      | Assign (name, idxs, expr) -> 
        let (st, i, o, idxs) = Expr.eval_list env conf idxs in
        let (st, i, o, Some value) = Expr.eval env (st, i, o, None) expr in
        eval env (update st name value idxs, i, o, Some value) Skip k
      | Seq (s1, s2) -> eval env conf (combine_continuation k s2) s1
      | Skip -> (match k with
        | Skip -> conf
        | _ -> eval env conf Skip k)
      | If (cond, st1, st2) ->
        let (u_st, u_i, u_o, Some cond_value) = Expr.eval env conf cond in
        if (Value.to_int cond_value) != 0 
          then eval env (u_st, u_i, u_o, None) k st1
          else eval env (u_st, u_i, u_o, None) k st2
      | While (cond, body) ->
        let (u_st, u_i, u_o, Some cond_value) = Expr.eval env conf cond in
        if (Value.to_int cond_value) != 0
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
          name:IDENT idxs:(-"[" !(Expr.parse) -"]")* ":=" expr:!(Expr.parse) { Assign (name, idxs, expr) }
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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
