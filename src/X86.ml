(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

let set_zero operand = Binop ("^", operand, operand)

let create_binop op x y = Binop (op, x, y)

let rec compile_cmp env l r op res_operand =
  let op_suffix ops = (
    match ops with
      | "<=" -> "le"
      | "<" -> "l"
      | ">=" -> "ge"
      | ">" -> "g"
      | "==" -> "e"
      | "!=" -> "ne"
      | _ -> failwith (Printf.sprintf "Unknown operator %s" ops)
  ) in 
  match (l, r) with
    | (S _, S _) -> [
      set_zero eax;
      Mov (l, edx);
      Binop ("cmp", r, edx);
      Set(op_suffix op, "%al");
      Mov(eax, res_operand)
    ]
    | _ -> [
      set_zero eax;
      Binop ("cmp", r, l);
      Set (op_suffix op, "%al");
      Mov (eax, res_operand)
    ]

let rec compile_binop env l r op res_operand =
  let set_zero operand = Binop("^", operand, operand) in
  let compile_simple_arithm op = (
    match (l, r) with
      | (S _, S _) -> [
          Mov (l, eax);
          Binop (op, r, eax);
          Mov (eax, res_operand)
      ]
      | _ -> if res_operand = l
        then [
          Binop (op, r, l)
        ]
        else [
          Binop (op, r, l);
          Mov (l, res_operand)
        ]
  ) in
  let compile_div_mod op = (
    let result = if op = "/" then eax else edx in
      [
        Mov (l, eax);
        set_zero edx;
        Cltd;
        IDiv r;
        Mov (result, res_operand)
      ]
  ) in
  let compile_or op = [
    set_zero eax;
    Mov (l, edx);
    Binop ("!!", r, edx);
    Set ("nz", "%al");
    Mov (eax, res_operand)
  ] in
  let compile_and op = [
    set_zero eax;
    set_zero edx;
    Binop ("cmp", L 0, l);
    Set ("ne", "%al");
    Binop ("cmp", L 0, r);
    Set ("ne", "%dl");
    Binop ("&&", edx, eax);
    Mov (eax, res_operand)
  ] in
  let asm = match op with
    | "+" | "-" | "*" -> compile_simple_arithm op
    | "/" | "%" -> compile_div_mod op
    | "<=" | "<" | ">=" | ">" | "==" | "!=" -> compile_cmp env l r op res_operand
    | "!!" -> compile_or op
    | "&&" -> compile_and op
    | _ -> failwith ("Unknown operand") in
  env, asm

let rec range l h = if l >= h then [] else l :: (range (l + 1) h)

let rec compile_single env instr =
  let push_all_regs_on_stack = List.map (fun x -> Push (R x)) (range 0 num_of_regs) in
  let pop_all_regs_from_stack = List.map (fun x -> Pop (R x)) (List.rev (range 0 num_of_regs)) in
  let get_operands env num = (
    let accumulate = (fun (env, operands) _ -> let operand, env = env#pop in (env, operand::operands)) in
    List.fold_left accumulate (env, []) (range 0 num)) in
  let env, asm = match instr with
    | CONST x ->
      let operand, env = env#allocate in
      env, [Mov (L x, operand)]
    | BINOP op -> 
      let r, l, env = env#pop2 in
      let res_operand, env = env#allocate in
      (compile_binop env l r op res_operand)
    | READ ->
      let operand, env = env#allocate in
      env, [Call "Lread"; Mov (eax, operand)]
    | WRITE ->
      let operand, env = env#pop in 
      env, [Push operand; Call "Lwrite"; Pop eax]
    | LD name -> 
      let operand, env = (env#global name)#allocate in
      let var = env#loc name in
      env, [Mov (var, eax); Mov (eax, operand)]
    | ST name -> 
      let operand, env = (env#global name)#pop in
      let var = env#loc name in
      env, [Mov (operand, eax); Mov (eax, var)]
    | LABEL l -> env, [Label l]
    | JMP l -> env, [Jmp l]
    | CJMP (z, l) ->
      let operand, env = env#pop in
      env, [Binop ("cmp", L 0, operand); CJmp (z, l)]
    | BEGIN (name, args, locals) ->
      let env = env#enter name args locals in
      env, [Push ebp; Mov (esp, ebp)] @ push_all_regs_on_stack @ [Binop ("-", M ("$" ^ env#lsize), esp)]
    | END ->
      let return = [Mov (ebp, esp); Pop ebp; Ret; Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))] in
      env, [Label env#epilogue] @ pop_all_regs_from_stack @ return
    | CALL (name, num_args, is_procedure) ->
      let env', arg_operands = get_operands env num_args in
      let push_args = List.map (fun arg -> Push arg) arg_operands in
      let env'', res_asm = 
          if is_procedure 
            then let operand, env'' = env'#allocate in env'', [Mov (eax, operand)]
            else env', [] in
      env'', push_args @ [Call name; Binop ("+", L (num_args * word_size), esp)] @ res_asm  
    | RET has_ret ->
      if has_ret
        then let operand, env = env#pop in env, [Mov (operand, eax); Jmp env#epilogue]
        else env, [Jmp env#epilogue]
    | _ -> failwith "Unknown instruction"
  in env, asm

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let rec compile env prg = match prg with
  | [] -> env, []
  | instr :: rest ->
    let env, single_asm = compile_single env instr in
    let env, rest_asm = compile env rest in
      env, single_asm @ rest_asm

(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (range 0 (List.length l))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+1
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
