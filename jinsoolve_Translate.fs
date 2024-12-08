module Translate

open System.Linq
open AST
open IR
open Helper
open State

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
  
// Find the type of variable 'vname'
let getVarType (symtab: SymbolTable) (vname: Identifier) : CType =
  match Map.tryFind vname symtab with
  | Some (_, ctype) -> ctype  // vname을 찾으면 해당 타입을 반환
  | None -> failwith ("Unbound variable: " + vname)  // vname이 없으면 예외 발생

let rec transExp (symtab: SymbolTable) (e: Exp) : Register * Instr list =
  match e with
  | Null ->
      let r = createRegName ()
      (r, [Set (r, Imm 0)])
  | Num i ->
      let r = createRegName ()
      (r, [Set (r, Imm i)])
  | Boolean b ->
      let r = createRegName()
      if b then (r, [Set (r, Imm 1)])
      else (r, [Set (r, Imm 0)])
  | Var vname ->
      let varReg = lookupVar symtab vname // Contains the address of 'vname'
      let r = createRegName ()

      (r, [Load (r, varReg)])
  | Deref vname -> // Ex) "*x"
    let varReg = lookupVar symtab vname // Contains the address of 'vname'
    let r = createRegName()
    let r_addr = createRegName()
    
    (r, [Load (r_addr, varReg) ; Load(r, r_addr)])
  | AddrOf vname -> // Ex) "&x"
    let varReg = lookupVar symtab vname // 주소
    let r = createRegName ()
    
    (r, [Set(r, Reg varReg)]) // 주소를 그대로 저장
  | Arr (vname, e) -> // Ex) "x[E]"
    let varReg = lookupVar symtab vname   
    
    let idxReg, idxInstr = transExp symtab e // e는 index
    let offsetReg = createRegName()
    let arrType = getVarType symtab vname
    let size =
      match arrType with
      | CIntArr _ -> 4
      | CBoolArr _ -> 1
      | _ -> failwith "Invalid array type"
    
    let r = createRegName() // 결과 register
    
    (r,
     idxInstr
     @ [BinOp (offsetReg, MulOp, Reg idxReg, Imm size)]
     @ [BinOp (offsetReg, AddOp, Reg offsetReg, Reg varReg)]
     @ [Load (r, offsetReg)])
    
  | Neg e -> // -E
    let e_r, e_i = transExp symtab e
    let r = createRegName()
    (r, e_i @ [UnOp (r, NegOp, Reg e_r)])
  | Add(e1, e2) -> // E + E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, AddOp, Reg r1, Reg r2)])
  | Sub(e1, e2) -> // E - E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, SubOp, Reg r1, Reg r2)])
  | Mul(e1,e2) -> // E * E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, MulOp, Reg r1, Reg r2)])
  | Div(e1,e2) -> // E / E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, DivOp, Reg r1, Reg r2)])
  | Equal(e1,e2) -> // E == E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, EqOp, Reg r1, Reg r2)])
  | NotEq(e1,e2) -> // E != E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, NeqOp, Reg r1, Reg r2)])
  | LessEq(e1,e2) -> // E <= E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, LeqOp, Reg r1, Reg r2)])
  | LessThan(e1,e2) -> // E < E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, LtOp, Reg r1, Reg r2)])
  | GreaterEq(e1,e2) -> // E >= E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, GeqOp, Reg r1, Reg r2)])
  | GreaterThan(e1,e2) -> // E > E
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    (r, i1 @ i2 @ [BinOp(r, GtOp, Reg r1, Reg r2)])
  | And(e1,e2) -> // E && E
    (*
    [i1]
    if (not e1) goto L1
    [i2]
    if (not e2) goto L1
    [True]
    goto L2
    L1
    [False]
    L2
    *)
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    
    let L1 = createLabel()
    let L2 = createLabel()
    
    (r,
     i1
     @ [GotoIfNot(Reg r1, L1)]
     @ i2
     @ [GotoIfNot(Reg r2, L1)]
     @ [Set(r, Imm 1)] // true
     @ [Goto(L2)]
     @ [Label L1]
     @ [Set(r, Imm 0)] // false
     @ [Label L2])
    
  | Or(e1, e2) -> // E || E
    (*
    if(e1) goto L1
    if(e2) goto L1
    [Set False]
    [goto L2]
    [Label L1]
    [Set True]
    [Label L2]
    *)
    let r1, i1 = transExp symtab e1
    let r2, i2 = transExp symtab e2
    let r = createRegName()
    
    let L1 = createLabel()
    let L2 = createLabel()
    
    (r,
     i1
     @ [GotoIf(Reg r1, L1)]
     @ i2
     @ [GotoIf(Reg r2, L1)]
     @ [Set(r, Imm 0)] // false
     @ [Goto(L2)]
     @ [Label L1]
     @ [Set(r, Imm 1)] // true
     @ [Label L2])
    
  | Not(e) -> // !E
    let e_r, e_i = transExp symtab e
    let r = createRegName()
    (r, e_i @ [BinOp(r, EqOp, Reg e_r, Imm 0)])
  | _ -> ("", []) // TODO: Fill in the remaining cases to complete the code.

let rec transStmt (symtab: SymbolTable) stmt : SymbolTable * Instr list =
  match stmt with
  | Declare (_, typ, vname) ->
    let r = createRegName ()
    let size = sizeof typ
    let symtab = Map.add vname (r, typ) symtab
    (symtab, [LocalAlloc (r, size)])
  | Define (_, typ, vname, exp) ->
    let exp_r, exp_ins = transExp symtab exp // transExp 함수로 exp의 값을 알아내 보자.
    
    let r = createRegName() // 레지스터 이름 하나 만들어주고
    let size = sizeof typ // 해당 타입을 선언할 공간을 위한 크기를 알아보고
    let symtab = Map.add vname (r,typ) symtab // vname → (r,typ) 형태의 매핑을 symtab에 새로 넣어준다.
    
    (symtab, exp_ins @ [LocalAlloc (r, size); Store(Reg exp_r, r)]) // Set(r, Reg exp_r)
  | Assign (_, vname, exp) ->
    let exp_r, exp_ins = transExp symtab exp // exp의 register와 instruction 찾기
    let r = lookupVar symtab vname // symtab에서 vname 찾아본다
     
    (symtab, exp_ins @ [Store(Reg exp_r, r)])
    
  | PtrUpdate(_, vname, exp) ->
    let exp_r, exp_i = transExp symtab exp
    let r = lookupVar symtab vname
    let r_tmp = createRegName()
    
    (symtab, exp_i @ [Load(r_tmp, r); Store(Reg exp_r, r_tmp)])
  | ArrUpdate(_, vname, e1, e2) ->
    let arr_r = lookupVar symtab vname
    let arr_type = getVarType symtab vname
    let offset_r = createRegName()
    let size =
      match arr_type with
      | CIntArr _ -> 4
      | CBoolArr _ -> 1
      | _ -> failwith "Invalid array type"
    
    let idx_r, idx_i = transExp symtab e1
    let val_r, val_i = transExp symtab e2
    
    (symtab,
     idx_i
     @ val_i
     @ [BinOp(offset_r, MulOp, Reg idx_r, Imm size)]
     @ [BinOp(offset_r, AddOp, Reg offset_r, Reg arr_r)]
     @ [Store(Reg val_r, offset_r)])
  | Return (_, e) ->
    let e_r, e_i = transExp symtab e
    (symtab, e_i @ [Ret(Reg e_r)])
  | If (_, e, s1, s2) ->
    (*
    if (e) -> goto L1
    [I2 : inst. of s2]
    [Goto L2]
    [Label L1]
    [I1 : inst. of s1]
    [Label L2]
    *)
    let e_r, e_i = transExp symtab e
    let I2 = transStmts symtab s2
    let I1 = transStmts symtab s1
    let L1 = createLabel()
    let L2 = createLabel()
    
    (symtab, e_i @ [GotoIf (Reg e_r, L1)] @ I2 @ [Goto(L2) ; Label L1] @ I1 @ [Label L2])
    
  | While (_, e, s) ->
    (*
    if (not e) → goto L2
    [Label L1]
    [I : inst. of S]
    [e를 한 번 더 계산]
    if (e) → goto L1
    [Label L2]
    *)
    let e_r, e_i = transExp symtab e
    let I = transStmts symtab s
    let L1 = createLabel()
    let L2 = createLabel()
    (symtab, e_i @ [GotoIfNot(Reg e_r, L2) ; Label L1] @ I @ e_i @ [GotoIf(Reg e_r, L1) ; Label L2])
  | _ -> (symtab, []) // TODO: Fill in the remaining cases to complete the code.

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
      let accInstrs = [LocalAlloc (r, size); Store (Reg argName, r)] @ accInstrs
      transArgs accSymTab accInstrs tailArgs

// Translate input program into IR code.
let run (prog: Program) : IRCode =
  let (_, fname, args, stmts) = prog
  let argRegs = List.map snd args
  let symtab, argInstrs = transArgs Map.empty [] args
  let bodyInstrs = transStmts symtab stmts
  (fname, argRegs, argInstrs @ bodyInstrs)