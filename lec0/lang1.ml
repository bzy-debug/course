(* Abstract Syntax *)

type expr =
  | Cst of int
  | Add of expr * expr
  | Mul of expr * expr
  | Var of string
  | Let of string * expr * expr

(* Interpreter *)
let rec eval_expr expr env =
    match expr with
  | Cst i -> i
  | Add (e1, e2) -> eval_expr e1 env + eval_expr e2 env
  | Mul (e1, e2) -> eval_expr e1 env * eval_expr e2 env
  | Var x -> List.assoc x env
  | Let (x, bind, body) -> 
      let bind_val = eval_expr bind env in
        eval_expr body ((x, bind_val)::env)

(* Test *)
let expr0 = Cst 42
let expr1 = Mul(Cst 2, Cst 21)
let expr2 = Add(expr1, expr1)
let expr3 = Let("x", Cst 2, Let("y", Cst 3, Add(Var "x", Var "y")))
let expr4 = Let("x", Cst 3, Let("x", Cst 4, Mul(Var "x", Var "x")))
let _ = 
  assert (eval_expr expr0 [] = 42);
  assert (eval_expr expr1 [] = 42);
  assert (eval_expr expr2 [] = 84);
  assert (eval_expr expr3 [] = 5);
  assert (eval_expr expr4 [] = 16);

(* Nameless *)
module Nameless = struct
  type expr =
    | Cst of int
    | Add of expr * expr
    | Mul of expr * expr
    | Var of int
    | Let of expr * expr
end

(* Nameless Interpreter *)

let rec eval_nameless_expr (expr: Nameless.expr) env =
  match expr with
  | Cst i -> i
  | Add (e1, e2) -> eval_nameless_expr e1 env + eval_nameless_expr e2 env
  | Mul (e1, e2) -> eval_nameless_expr e1 env * eval_nameless_expr e2 env
  | Var i -> List.nth env i
  | Let (e1, e2) ->
      let e1_v = eval_nameless_expr e1 env in
        eval_nameless_expr e2 (e1_v :: env)

let nameless_expr0: Nameless.expr = Cst 42
let nameless_expr1: Nameless.expr = Mul(Cst 2, Cst 21)
let nameless_expr2: Nameless.expr = Add(nameless_expr1, nameless_expr1)
let nameless_expr3: Nameless.expr = Let(Cst 2, Let(Cst 3, Add(Var 1, Var 0)))
let nameless_expr4: Nameless.expr = Let(Cst 3, Let(Cst 4, Mul(Var 0, Var 0)))
let nameless_expr5: Nameless.expr = Let(Add(Cst 1, Cst 2), Let(Cst 4, Mul(Var 1, Var 0)))
let _ = 
  assert (eval_nameless_expr nameless_expr0 [] = 42);
  assert (eval_nameless_expr nameless_expr1 [] = 42);
  assert (eval_nameless_expr nameless_expr2 [] = 84);
  assert (eval_nameless_expr nameless_expr3 [] = 5);
  assert (eval_nameless_expr nameless_expr4 [] = 16);
  assert (eval_nameless_expr nameless_expr5 [] = 12)




(* Lowering *)
let index l x =
  let rec index_aux l x acc = 
      match l with
    | y :: tl ->
        if x = y then acc
        else index_aux tl x (acc + 1)
    | [] -> failwith "index"
  in index_aux l x 0

let rec lowering expr cenv =
  match expr with
  | Cst i -> Nameless.Cst i
  | Add (e1, e2) -> Nameless.Add(lowering e1 cenv, lowering e2 cenv)
  | Mul (e1, e2) -> Nameless.Mul(lowering e1 cenv, lowering e2 cenv)
  | Var x -> Nameless.Var(index cenv x)
  | Let (x, bind, body) ->
      Nameless.Let(lowering bind cenv, lowering body (x::cenv))

(* Test *)
let _ =
  assert ((lowering expr0 []) = nameless_expr0);
  assert ((lowering expr1 []) = nameless_expr1);
  assert ((lowering expr2 []) = nameless_expr2);
  assert ((lowering expr3 []) = nameless_expr3);
  assert ((lowering expr4 []) = nameless_expr4)

(* Instruction *)
type instr = Cst of int | Add | Mul

let rec eval_instr (instrs: instr list) stack =
  match (instrs, stack) with
  | ([], v::[]) -> v
  | (Cst i::rest, _) -> eval_instr rest (i::stack)
  | (Add::rest, v1::v2::stk) -> eval_instr rest (v1+v2::stk)
  | (Mul::rest, v1::v2::stk) -> eval_instr rest (v1*v2::stk)
  | _ -> assert false

let rec compile_nameless (expr: Nameless.expr) vars =
  match expr with
  | Cst i -> [Cst i]
  | Add (e1, e2) -> compile_nameless e1 vars @ compile_nameless e2 vars @ [Add]
  | Mul (e1, e2) -> compile_nameless e1 vars @ compile_nameless e2 vars @ [Mul]
  | Var i -> List.nth vars i
  | Let (e1, e2) -> let e1_i = compile_nameless e1 vars in compile_nameless e2 (e1_i::vars)

let _ =
  assert ((eval_instr (compile_nameless nameless_expr0 []) []) = 42);
  assert ((eval_instr (compile_nameless nameless_expr1 []) []) = 42);
  assert ((eval_instr (compile_nameless nameless_expr2 []) []) = 84);
  assert ((eval_instr (compile_nameless nameless_expr3 []) []) = 5);
  assert ((eval_instr (compile_nameless nameless_expr4 []) []) = 16);
  assert ((eval_instr (compile_nameless nameless_expr5 []) []) = 12)

(* Instruction With Variable*)
type instr_var = Cst of int | Add | Mul | Var of int | Pop | Swap

(* Interpreter *)
let rec eval_instr_var instrs stack =
  match (instrs, stack) with
  | ([], v::[]) -> v
  | (Cst i::rest, _) -> eval_instr_var rest (i::stack)
  | (Add::rest, v1::v2::stk) -> eval_instr_var rest (v1+v2 :: stk)
  | (Mul::rest, v1::v2::stk) -> eval_instr_var rest (v1*v2 :: stk)
  | (Var i::rest, _) -> eval_instr_var rest ((List.nth stack i)::stack)
  | (Pop::rest, _::stk) -> eval_instr_var rest stk
  | (Swap::rest, n1::n2::stk) -> eval_instr_var rest (n2::n1::stk)
  | _ -> assert false

(* Test *)
let instrs0 = [Cst 42]
let instrs1 = [Cst 2; Cst 21; Mul]
let instrs2 = instrs1 @ instrs1 @ [Add]
let instrs3 = [Cst 17; Var 0; Var 1; Add; Swap; Pop]
let instrs4 = [Cst 1; Cst 2; Var 0; Cst 7; Add; Swap; Pop; Add]
let _ = 
  assert (eval_instr_var instrs0 [] = 42);
  assert (eval_instr_var instrs1 [] = 42);
  assert (eval_instr_var instrs2 [] = 84);
  assert (eval_instr_var instrs3 [] = 34);
  assert (eval_instr_var instrs4 [] = 10)

(* Compile *)
let rec compile_exp (exp: expr) v_pos sp =
  match exp with
  | Cst i -> [Cst i]
  | Add(e1, e2) -> compile_exp e1 v_pos sp @
                   compile_exp e2 v_pos (sp+1) @ [Add]
  | Mul(e1, e2) -> compile_exp e1 v_pos sp @
                   compile_exp e2 v_pos (sp+1) @ [Mul]
  | Var x -> [Var (sp - (List.assoc x v_pos) - 1)]
  | Let (x, e1, e2) -> compile_exp e1 v_pos sp @ compile_exp e2 ((x, sp)::v_pos) (sp+1) @ [Swap; Pop]

let expr5:expr = Let("x", Cst 17, Add(Var "x", Var "x"))
let expr6:expr = Add(Cst 1, Let("x", Cst 2, Add(Var "x", Cst 7)))
let expr7:expr = Add(Cst 1, Let("x", Mul(Cst 12, Cst 2), Add(Var "x", Cst 7)))
let _ = 
  assert (instrs3 = compile_exp expr5 [] 0);
  assert (instrs4 = compile_exp expr6 [] 0)

let rec var_instr2instr var_instrs stack =
  match var_instrs with
  | Cst i :: rest -> Cst i :: var_instr2instr rest vars
  | 