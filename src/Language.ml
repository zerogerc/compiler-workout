(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a                                          

    let string_val v =
      let buf      = Buffer.create 128 in
      let append s = Buffer.add_string buf s in
      let rec inner = function
      | Int    n    -> append (string_of_int n)
      | String s    -> append "\""; append @@ Bytes.to_string s; append "\""
      | Array  a    -> let n = Array.length a in
                       append "["; Array.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append "]"
      | Sexp (t, a) -> let n = List.length a in
                       append "`"; append t; (if n > 0 then (append " ("; List.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append ")"))
      in
      inner v;
      Bytes.of_string @@ Buffer.contents buf
                      
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "raw"      -> (st, i, o, Some (Value.of_int 1))
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [j; b] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | ".string" | ".stringval" -> 
      let rec to_string value = 
        match value with
        | (Value.Int n) -> string_of_int n
        | (Value.String b) -> Printf.sprintf "\"%s\"" (Bytes.to_string b)
        | (Value.Array elems) -> Printf.sprintf "[%s]" (String.concat ", " (List.map to_string (Array.to_list elems)))
        | (Value.Sexp (name, elems)) -> match elems with
          | [] -> Printf.sprintf "`%s" name
          | _ -> Printf.sprintf "`%s (%s)" name (String.concat ", " (List.map to_string elems)) in 
        (st, i, o, Some (Value.String (Bytes.of_string (to_string (List.hd args)))))
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
    (* integer constant   *) | Const     of int
    (* array              *) | Array     of t list
    (* string             *) | String    of string
    (* S-expressions      *) | Sexp      of string * t list
    (* variable           *) | Var       of string
    (* binary operator    *) | Binop     of string * t * t
    (* element extraction *) | Elem      of t * t
    (* length             *) | Length    of t
    (* string conversion  *) | StringVal of t
    (* function call      *) | Call      of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
    
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
      | Const n -> (st, i, o, Some (Value.of_int n))
      | Array exprs -> 
        let (st, i, o, values) = eval_list env conf exprs in
        env#definition env ".array" values (st, i, o, None)
      | String s -> (st, i, o, Some (Value.of_string (Bytes.of_string s)))
      | Sexp (name, exps) ->
        let (st, i, o, values) = eval_list env conf exps in
        (st, i, o, Some (Value.Sexp (name, values)))
      | Var name -> (st, i, o, Some (State.eval st name))
      | Binop (op, x, y) -> 
        let st, i, o, Some (Value.Int v1) = eval env conf x in
        let st, i, o, Some (Value.Int v2) = eval env (st, i, o, None) y in
        (st, i, o, Some (Value.of_int (to_func op v1 v2)))
      | Elem (arr_expr, idx_expr) ->
        let (st, i, o, values) = eval_list env conf [idx_expr; arr_expr] in
        env#definition env ".elem" values (st, i, o, None)
      | Length arr_expr -> 
        let (st, i, o, Some arr) as conf = eval env conf arr_expr in
        env#definition env ".length" [arr] (st, i, o, None)
      | StringVal expr -> 
        let st, i, o, Some value = eval env conf expr
        in env#definition env ".stringval" [value] (st, i, o, None)
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
          (Array.map 
            (fun (a, s) -> a, List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s) 
            [|                
              `Lefta, ["!!"];
              `Lefta, ["&&"];
              `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
              `Lefta, ["+" ; "-"];
              `Lefta, ["*" ; "/"; "%"];
            |] 
          )
          arr_expr
        );
      
      arr_expr:
        idx:(
          a:indexed length:".length"? { match length with | Some _ -> Length a | None -> a }
        )
        str:".string"? { match str with | Some _ -> StringVal idx | None -> idx };

      indexed: e:primary idx:indices { List.fold_left (fun e id -> Elem (e, id)) e idx};
      
      indices: idx:((-"[" parse -"]")*) {idx};

      primary:
        n:DECIMAL { Const n }
        | c:CHAR { Const (Char.code c) }
        | str:STRING { String (String.sub str 1 (String.length str - 2)) }
        | -"(" parse -")"
        | name:IDENT "(" args:!(Util.list0 parse) ")" { Call (name, args) }
        | name:IDENT { Var name }
        | "[" exprs:!(Util.list0 parse) "]" { Array exprs }
        | "`" name:IDENT subs:((-"(" (!(Util.list)[parse]) -")")?) { match subs with Some subs -> Sexp (name, subs) | None -> Sexp (name, []) }
    )    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse: wildcard | sexp | var;
          
          wildcard: "_" { Wildcard };
          sexp: "`" name:IDENT subs_opt:((-"(" (!(Util.list)[parse]) -")")?) {
            match subs_opt with 
              | Some subs -> Sexp (name, subs) 
              | None -> Sexp (name, [])
          };
          var: name:IDENT { Ident name }
        )
        
        let vars p = transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
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
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st


    let rec pattern_match value brs = 
      let is_some = function | Some _ -> true | None -> false in
      let rec bind_pattern_variables value pattern = match pattern with
        | Pattern.Wildcard -> Some []
        | Pattern.Sexp (name, subpatterns) ->
          let Value.Sexp (name', subvalues) = value in
            if (name = name') && (List.length subpatterns = List.length subvalues) then
              let subresults = List.map2 bind_pattern_variables subvalues subpatterns in
              match (List.for_all (is_some) subresults) with 
                | true -> Some (List.concat (List.map (fun (Some lst) -> lst) subresults)) 
                | false -> None
            else None 
        | Pattern.Ident var -> Some [(var, value)] in
      let match_pattern (pattern, stmt) = match (bind_pattern_variables value pattern) with 
        | Some lst -> Some (lst, stmt) 
        | None -> None in
      let Some (branch_locals, stmt) = List.find (is_some) (List.map match_pattern brs) in
      branch_locals, stmt

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
        eval env (update st name value idxs, i, o, None) Skip k
      | Seq (s1, s2) -> eval env conf (combine_continuation k s2) s1
      | Skip -> (match k with
        | Skip -> conf
        | _ -> eval env conf Skip k)
      | If (cond, st1, st2) ->
        let (u_st, u_i, u_o, Some (Value.Int cond_value)) = Expr.eval env conf cond in
        if cond_value != 0 
          then eval env (u_st, u_i, u_o, None) k st1
          else eval env (u_st, u_i, u_o, None) k st2
      | While (cond, body) ->
        let (u_st, u_i, u_o, Some (Value.Int cond_value)) = Expr.eval env conf cond in
        if cond_value != 0
          then eval env (u_st, u_i, u_o, None) (combine_continuation k stmt) body 
          else eval env (u_st, u_i, u_o, None) Skip k
      | Case (expr, brs) ->
        let st, i, o, Some value = Expr.eval env (st, i, o, None) expr in
        let br_locals, stmt = pattern_match value brs in
        let br_var_names, _ = List.split br_locals in
        let st = State.push st State.undefined br_var_names in
        let st = List.fold_left (fun st (name, value) -> State.update name value st) st br_locals in
        let st, i, o, res = eval env (st, i, o, None) Skip stmt in
        let st = State.drop st in
        eval env (st, i, o, res) Skip k
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
        | "return" expr:!(Expr.parse)? { Return expr }
        | "case" value:!(Expr.parse) "of" branches:(!(Util.listBy)[ostap ("|")][case_branch]) "esac" { Case (value, branches) };

      eliffi:
        "fi" { Skip }
        | "else" st:parse "fi" { st }
        | "elif" cond:!(Expr.parse) "then" st1:parse st2:eliffi { If (cond, st1, st2) };
      
      case_branch: p:!(Pattern.parse) "->" stmt:parse { (p, stmt) }
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
             let xs, locs, s      = snd @@ M.find f m in
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
