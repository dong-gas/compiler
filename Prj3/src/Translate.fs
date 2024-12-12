module Translate

open AST
open IR
open Helper

let trash = "trash"

// Symbol table is a mapping from identifier to a pair of register and type.
// Register is recorded here will be containg the address of that variable.
type SymbolTable = Map<Identifier,Register * CType>

// Let's assume the following size for each data type.
let sizeof (ctyp: CType) =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntPtr -> 8
  | CBoolPtr -> 8
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

// Find the register that contains pointer to variable 'vname'
let lookupVar (symtab: SymbolTable) (vname: Identifier) : Register =
  let _ = if not (Map.containsKey vname symtab) then failwith "Unbound variable"
  fst (Map.find vname symtab)
  
let lookupType (symtab: SymbolTable) (vname: Identifier) : CType =
    let _ = if not (Map.containsKey vname symtab) then failwith "Unbound variable"
    snd (Map.find vname symtab)

let rec transExp (symtab: SymbolTable) (e: Exp) : Register * Instr list = // 변수 저장된 레지스터와 instrlist 리턴
  match e with
  | Null ->
      let r = createRegName ()
      (r, [Set (r, Imm 0)])
  | Num i ->
      let r = createRegName ()
      (r, [Set (r, Imm i)])
  | Boolean b ->
      let r = createRegName ()
      match b with
      | true -> (r, [Set(r, Imm 1)])
      | false -> (r, [Set(r, Imm 0)])
  | Var vname -> // x
      let varReg = lookupVar symtab vname // Contains the address of 'vname'
      let r = createRegName ()
      (r, [Load (r, varReg)])
  | Deref vname -> // *x
      let varReg = lookupVar symtab vname
      let r = createRegName ()
      let tmp = createRegName ()
      (r, [Load (tmp, varReg)] @ [Load(r, tmp)])
  | AddrOf vname -> // &x
      let varReg = lookupVar symtab vname
      let r = createRegName ()
      (r, [Label varReg] @ [Set(r, Reg varReg)])
  | Arr (vname, exp) -> // x[exp]
      let varReg = lookupVar symtab vname
      let idx_r, idx_instr_list = transExp symtab exp
      let sz =
          match (lookupType symtab vname) with
          | CBoolArr _-> 1
          | CIntArr _ -> 4
          | _ -> 0
      let r = createRegName ()
      let tmp = createRegName ()
      let mul_instr = BinOp(tmp, MulOp, Reg idx_r, Imm sz)
      let add_instr = BinOp(tmp, AddOp, Reg varReg, Reg tmp)
      (r, idx_instr_list @ [mul_instr] @ [add_instr] @ [Load(r, tmp)]) 
  | Neg exp -> // -E
      let r, exp_instr_list = transExp symtab exp
      let reg = createRegName ()
      (reg, exp_instr_list @ [UnOp(reg, NegOp, Reg r)])
  | Add (exp1, exp2) -> // E + E
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, AddOp, Reg r1, Reg r2)])
  | Sub (exp1, exp2) -> // E - E
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, SubOp, Reg r1, Reg r2)])
  | Mul (exp1, exp2) -> // E * E
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, MulOp, Reg r1, Reg r2)])
  | Div (exp1, exp2) -> // E / E
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, DivOp, Reg r1, Reg r2)])
  | Equal (exp1, exp2) -> // e == e
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, EqOp, Reg r1, Reg r2)])
  | NotEq (exp1, exp2) -> // !=
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, NeqOp, Reg r1, Reg r2)])
  | LessEq (exp1, exp2) -> // <=
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, LeqOp, Reg r1, Reg r2)])
  | LessThan (exp1, exp2) -> // <
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, LtOp, Reg r1, Reg r2)])
  | GreaterEq (exp1, exp2) ->  // >=
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, GeqOp, Reg r1, Reg r2)])
  | GreaterThan (exp1, exp2) -> // >
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let reg = createRegName ()
      (reg, exp_instr_list_1 @ exp_instr_list_2 @ [BinOp(reg, GtOp, Reg r1, Reg r2)])
  | And (exp1, exp2) -> // &&
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let L = createLabel ()
      (r2, exp_instr_list_1 @ [Set(r2, Imm 0)] @ [GotoIfNot(Reg r1, L)] @ exp_instr_list_2 @ [Label L])
  | Or (exp1, exp2) -> // ||
      let r1, exp_instr_list_1 = transExp symtab exp1
      let r2, exp_instr_list_2 = transExp symtab exp2
      let L = createLabel ()
      (r2, exp_instr_list_1 @ [Set (r2,Imm 1)] @ [GotoIf(Reg r1, L)] @ exp_instr_list_2 @ [Label L])
  | Not exp -> // !E
      let r, exp_instr_list = transExp symtab exp
      let reg = createRegName ()
      (reg, exp_instr_list @ [UnOp(reg, NotOp, Reg r)])

let rec transStmt (symtab: SymbolTable) stmt : SymbolTable * Instr list =
  match stmt with
  | Declare (_, typ, vname) -> // ex) int x;
      let r = createRegName ()
      let size = sizeof typ
      let symtab = Map.add vname (r, typ) symtab
      match typ with
      | CInt | CBool ->
          (symtab, [Label trash] @ [LocalAlloc (r, size)] @ [Label trash])
      | _ -> (symtab, [LocalAlloc (r, size)])
      
  | Define (_, typ, vname, exp) -> // ex) int x = 0;
      let r1 = createRegName ()
      let size = sizeof typ
      let symtab = Map.add vname (r1, typ) symtab
      let r2, exp_instr_list = transExp symtab exp
      match typ with
      | CInt | CBool ->
          (symtab, exp_instr_list @ [Label trash] @ [LocalAlloc(r1, size)] @ [Label trash] @[Store(Reg r2, r1)])
      | _ ->(symtab, exp_instr_list @ [LocalAlloc(r1, size)] @ [Store(Reg r2, r1)])
  | Assign (_, vname, exp) -> // ex) x = 10;      
      let r1 = lookupVar symtab vname
      let r2, exp_instr_list = transExp symtab exp
      (symtab, exp_instr_list @ [Store(Reg r2, r1)]) 
  | PtrUpdate (_, vname, exp) -> // ex) *x = 10;
      let r1 = lookupVar symtab vname
      let r2, exp_instr_list = transExp symtab exp
      let add_r = createRegName ()
      (symtab, exp_instr_list @ [Load(add_r, r1)] @ [Store(Reg r2, add_r)])
  | ArrUpdate (_, vname, exp1, exp2) -> // ex) x[1] = 2;
      let idx_r, idx_instr_list = transExp symtab exp1
      let val_r, val_instr_list = transExp symtab exp2
      let first_reg = lookupVar symtab vname
      let sz =
          match (lookupType symtab vname) with
          | CBoolArr _-> 1
          | CIntArr _ -> 4
          | _ -> 0
      let r = createRegName ()
      let mul_instr = [BinOp(r, MulOp, Reg idx_r, Imm sz)]
      let add_instr = [BinOp(r, AddOp, Reg first_reg, Reg r)]
      (symtab, idx_instr_list @ val_instr_list @ mul_instr @ add_instr @ [Store(Reg val_r, r)])
  | Return (_, exp) -> // ex) return 0;
      let r, exp_instr_list = transExp symtab exp      
      (symtab, exp_instr_list @ [Ret (Reg r)])
  | If (_, exp, stmtl1, stmtl2) -> // ex) if (E) { S } else { S }
      let r, exp_instr_list = transExp symtab exp
      let L1 = createLabel ()
      let L2 = createLabel ()
      (symtab, exp_instr_list @ [GotoIfNot(Reg r, L1)] @ (transStmts symtab stmtl1) @ [Goto(L2)] @ [Label L1] @ (transStmts symtab stmtl2) @ [Label L2])
  | While (_, exp, stmtl) -> // ex) while (E) { S }
      let r, exp_instr_list = transExp symtab exp
      let L1 = createLabel ()
      let L2 = createLabel ()
      (symtab, [Label L1] @ exp_instr_list  @ [GotoIfNot(Reg r, L2)] @ (transStmts symtab stmtl) @ [Goto L1] @ [Label L2])
    

and transStmts symtab stmts: Instr list =
  match stmts with
  | [] -> []
  | headStmt :: tailStmts ->
      let symtab, instrs = transStmt symtab headStmt
      instrs @ transStmts symtab tailStmts

// This code allocates memory for each argument and records information to the
// symbol table. Note that argument can be handled similarly to local variable.
let rec transArgs accSymTab accInstrs args =
  match args with
  | [] -> accSymTab, accInstrs
  | headArg :: tailArgs ->
      // In our IR model, register 'argName' is already defined at the entry.
      let (argTyp, argName) = headArg
      let r = createRegName ()
      let size = sizeof argTyp
      // From now on, we can use 'r' as a pointer to access 'argName'.
      let accSymTab = Map.add argName (r, argTyp) accSymTab
      let accInstrs = [Label trash; LocalAlloc (r, size); Label trash; Store (Reg argName, r)] @ accInstrs
      transArgs accSymTab accInstrs tailArgs

// Translate input program into IR code.
let run (prog: Program) : IRCode =
  let (_, fname, args, stmts) = prog
  let argRegs = List.map snd args
  let symtab, argInstrs = transArgs Map.empty [] args
  let bodyInstrs = transStmts symtab stmts
  (fname, argRegs, argInstrs @ bodyInstrs)