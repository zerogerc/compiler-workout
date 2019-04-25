open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(* drop values from stack and jmp  *) | DROPJMP of string * int
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let execute_instruction config instruction = 
  let stack, (state, inp, out) = config in
  let stmt_config = (state, inp, out) in
  match instruction with
    | BINOP op ->
        let y::x::rest = stack in 
        let value = Expr.to_func op (Value.to_int x) (Value.to_int y) in 
        (Value.of_int value)::rest, stmt_config 
    | CONST value -> (Value.of_int value)::stack, stmt_config
    | STRING value -> (Value.of_string (Bytes.of_string value))::stack, stmt_config
    | SEXP (tag, count) -> let values, rest = split count stack in ((Value.sexp tag @@ (List.rev values))::rest, stmt_config)
    | LD name -> (State.eval state name)::stack, (state, inp, out)
    | ST name -> (List.tl stack), (State.update name (List.hd stack) state, inp, out)
    | STA (name, size) -> 
      let (value::ids), rest = split (size + 1) stack in 
      rest, (Stmt.update state name value (List.rev ids), inp, out)
    | DROP -> (List.tl stack), stmt_config
    | DUP -> (List.hd stack)::stack, stmt_config
    | SWAP -> let x::y::rest = stack in y::x::rest, stmt_config
    | TAG t ->
      let x::rest = stack in
      let res = match x with
        | Value.Sexp (t', _) -> if (t = t') then 1 else 0
        | _ -> 0 in
      (Value.of_int res)::rest, stmt_config
    | _ -> failwith "Unknown instruction"

let rec eval env config program = 
  let (control_stack, stack, (state, i, o)) = config in
    match program with
    [] -> config
    | LABEL l :: rest -> eval env config rest
    | JMP l :: _ -> eval env config (env#labeled l)
    | CJMP (z, l) :: rest ->
        if (z = "z" && (Value.to_int (List.hd stack)) == 0 || z = "nz" && (Value.to_int (List.hd stack)) != 0)
          then eval env (control_stack, List.tl stack, (state, i, o)) (env#labeled l) 
          else eval env (control_stack, List.tl stack, (state, i, o)) rest
    | DROPJMP (l, depth) :: rest -> 
      let z::stack = stack in
      if Value.to_int z = 0 
        then let (_,  jmp_stack) = split depth stack in eval env (control_stack, jmp_stack, (state, i, o)) (env#labeled l)
        else eval env (control_stack, stack, (state, i, o)) rest
    | BEGIN (_, arg_names, local_names) :: rest -> 
      let fun_state = State.enter state (arg_names @ local_names) in
      let updated_state, updated_stack = 
        List.fold_left 
          (fun (s, value::rest) name -> (State.update name value s, rest))
          (fun_state, stack)
          (List.rev arg_names)
      in
      eval env (control_stack, updated_stack, (updated_state, i, o)) rest
    | (RET _ | END) :: _ -> (match control_stack with
      | (before_prg, before_state)::cs_rest -> 
        eval env (cs_rest, stack, (State.leave state before_state, i, o)) before_prg
      | _ -> config
    )
    | ENTER args :: rest ->
      let values, stack = split (List.length args) stack in
      let scope = List.fold_left (fun st (name, value) -> State.bind name value st) State.undefined (List.combine args values) in
      let state = (State.push state scope args) in
      eval env (control_stack, stack, (state, i, o)) rest
    | LEAVE :: rest -> eval env (control_stack, stack, (State.drop state, i, o)) rest
    | CALL (name, args_count, is_procedure) :: rest -> 
      if env#is_label name 
        then eval env ((rest, state)::control_stack, stack, (state, i, o)) (env#labeled name)
        else eval env (env#builtin (control_stack, stack, (state, i, o)) name args_count (is_procedure)) rest 
    | instruction::rest ->
      let updated_stack, updated_config = execute_instruction (stack, (state, i, o)) instruction in
      eval env (control_stack, updated_stack, updated_config) rest

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let label_generator =
  object (self)
    val mutable next = 0

    method generate = 
      next <- next + 1;
      ".label" ^ (string_of_int next)
  end

let rec compile_call name args is_procedure = 
  let compiled_args = List.flatten @@ List.map compile_expr args in
  compiled_args @ [CALL (name, List.length args, is_procedure)]

and compile_expr = function
  | Expr.Const n -> [CONST n]
  | Expr.Array exprs -> 
    let compiled_exprs = List.flatten (List.map compile_expr exprs) in
    compiled_exprs @ [CALL (".array", (List.length compiled_exprs), false)]
  | Expr.String s -> [STRING s]
  | Expr.Sexp (name, exprs) ->  
    let compiled_exprs = List.flatten (List.map compile_expr exprs) in
    compiled_exprs @ [SEXP (name, List.length exprs)]
  | Expr.Var x -> [LD x]
  | Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
  | Expr.Elem (arr, idx) -> compile_expr arr @ compile_expr idx @ [CALL (".elem", 2, false)]
  | Expr.Length arr -> compile_expr arr @ [CALL (".length", 1, false)]
  | Expr.Call (name, args) -> compile_call name args false

and make_bindings pattern =
  let rec inner p = match p with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident var -> [[]]
    | Stmt.Pattern.Sexp (_, exprs) -> 
      let next i x = List.map (fun arr -> i::arr) (inner x) in List.flatten (List.mapi next exprs)
  in
  let elem i = [CONST i; CALL (".elem", 2, false)] in
  let extract_bind_value path = [DUP] @ (List.flatten (List.map elem path)) @ [SWAP] in
  List.flatten (List.map extract_bind_value (List.rev (inner pattern)))

and compile_simple_branch pattern stmt next_label end_label =
  let pattern_prg, p_used = compile_pattern pattern next_label 0 in
  let stmt_prg, s_used = compile_block (Stmt.Seq (stmt, Stmt.Leave)) end_label in
  pattern_prg @ make_bindings pattern @ [DROP; ENTER (List.rev (Stmt.Pattern.vars pattern))] @ stmt_prg, p_used, s_used

and compile_pattern pattern end_label depth = 
  match pattern with
    | Stmt.Pattern.Wildcard -> [DROP], false
    | Stmt.Pattern.Ident _ -> [DROP], false
    | Stmt.Pattern.Sexp (name, exprs) ->
      let compile_subpattern i pattern = 
        let inner_prg = match pattern with
        | Stmt.Pattern.Sexp (_, ps) -> 
          if List.length ps > 0 
            then [DUP] @ fst (compile_pattern pattern end_label (depth + 1)) @ [DROP]
            else fst (compile_pattern pattern end_label depth)
        | _ -> fst (compile_pattern pattern end_label depth) 
        in  
        [DUP; CONST i; CALL (".elem", 2, false)] @ inner_prg in 
      let prg = List.flatten (List.mapi compile_subpattern exprs) in
      [TAG name] @ [DROPJMP (end_label, depth)] @ prg, true 

and compile_block stmt end_label =
  match stmt with
    | Stmt.Assign (name, idxs, e) -> (
      match idxs with
        | [] -> compile_expr e @ [ST name], false
        | idxs -> 
          let compiled_idxs = List.fold_left (fun comp e -> comp @ (compile_expr e)) [] idxs in
          compiled_idxs @ compile_expr e @ [STA (name, List.length idxs)], false)  
    | Stmt.Seq (s1, s2) -> 
      let l_end1 = label_generator#generate in
      let prg1, used1 = compile_block s1 l_end1 in
      let prg2, used2 = compile_block s2 end_label in
      prg1 @ (if used1 then [LABEL l_end1] else []) @ prg2, used2
    | Stmt.Skip -> [], false
    | Stmt.If (e, s1, s2) ->
      let l_else = label_generator#generate in
      let if_prg, used1 = compile_block s1 end_label in
      let else_prg, used2 = compile_block s2 end_label in
      compile_expr e @ [CJMP ("z", l_else)] @ if_prg @ [JMP end_label] @ [LABEL l_else] @ else_prg @ [JMP end_label], true
    | Stmt.While (e, s) ->
      let l_cond = label_generator#generate in
      let l_loop = label_generator#generate in
      let loop_prg, _ = compile_block s l_cond in
      [JMP l_cond; LABEL l_loop] @ loop_prg @ [LABEL l_cond] @ compile_expr e @ [CJMP ("nz", l_loop)], false
    | Stmt.Repeat (s, e) ->
      let l_repeat = label_generator#generate in
      let repeat_prg = compile_stmt s in
      [LABEL l_repeat] @ repeat_prg @ compile_expr e @ [CJMP ("z", l_repeat)], false
    | Stmt.Case (e, brs) -> (match brs with
      | [pattern, stmt] ->
        let br_prg, p_used, s_used = compile_simple_branch pattern stmt end_label end_label in 
        compile_expr e @ [DUP] @ br_prg, p_used || s_used 
      | brs ->
        let n = List.length brs - 1 in
        let compile_branch_fold (prev_label, i, prg) (pattern, p_stmt) =
          let has_next = (i != n) in
          let next_label = if has_next then label_generator#generate else end_label in
          let label_prg = match prev_label with Some x -> [LABEL x; DUP] | None -> [] in
          let br_prg, _, _ = compile_simple_branch pattern p_stmt next_label end_label in
          let cur_prg = label_prg @ br_prg @ (if has_next then [JMP end_label] else []) in
          Some next_label, i + 1, cur_prg :: prg in
        let _, _, prg = List.fold_left compile_branch_fold (None, 0, []) brs in
        compile_expr e @ [DUP] @ List.flatten @@ List.rev prg, true
    )
    | Stmt.Return e -> (match e with
      | Some v -> (compile_expr v) @ [RET true]
      | _ -> [RET false]), false
    | Stmt.Call (name, args) -> compile_call name args true, false
    | Stmt.Leave -> [LEAVE], false

and compile_stmt stmt =
  let end_label = label_generator#generate in
  let prg, used = compile_block stmt end_label in
  prg @ (if used then [LABEL end_label] else []) 

and compile_defs defs =
  List.fold_left 
  (fun prev (name, (args, locals, body)) -> 
    let compiled_body = compile_stmt body in 
    prev @ [LABEL name] @ [BEGIN (name, args, locals)] @ compiled_body @ [END]
  )
  []
  defs

and compile (defs, stmt) = 
  let compiled_stmt = compile_stmt stmt in
  let compiled_defs = compile_defs defs in
  compiled_stmt @ [END] @ compiled_defs