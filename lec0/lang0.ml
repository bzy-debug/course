(* Abstract Syntax *)

type expr =
  | Cst of int
  | Add of expr * expr
  | Mul of expr * expr

(* Interpreter *)
let rec eval_expr = function
  | Cst i -> i
  | Add (e1, e2) -> eval_expr e1 + eval_expr e2
  | Mul (e1, e2) -> eval_expr e1 * eval_expr e2

(* Test *)
let expr0 = Cst 42
let expr1 = Mul(Cst 2, Cst 21)
let expr2 = Add(expr1, expr1)
let test = 
  assert (eval_expr expr0 = 42);
  assert (eval_expr expr1 = 42);
  assert (eval_expr expr2 = 84)


(* Instruction *)
type instr = Cst of int | Add | Mul

(* Interpreter *)
let rec eval_instr instrs stack =
  match (instrs, stack) with
  | ([], v::[]) -> v
  | (Cst i::rest, _) -> eval_instr rest (i::stack)
  | (Add::rest, v1::v2::stk) -> eval_instr rest (v1+v2 :: stk)
  | (Mul::rest, v1::v2::stk) -> eval_instr rest (v1*v2 :: stk)
  | _ -> assert false

(* Test *)
let instrs0 = [Cst 42]
let instrs1 = [Cst 2; Cst 21; Mul]
let instrs2 = instrs1 @ instrs1 @ [Add]
let test_instr = 
  assert (eval_instr instrs0 [] = 42);
  assert (eval_instr instrs1 [] = 42);
  assert (eval_instr instrs2 [] = 84)
