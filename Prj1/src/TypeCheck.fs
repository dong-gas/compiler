module TypeCheck

open AST

// Symbol table is a mapping from 'Identifier' (string) to 'CType'. Note that
// 'Identifier' and 'Ctype' are defined in AST.fs file.
type SymbolTable = Map<Identifier, CType>

// For semantic analysis, you will need the following type definition. Note the
// difference between 'Ctype' and 'Typ': 'Ctype' represents the type annoted in
// the C code, whereas 'Typ' represents the type obtained during type checking.
type Typ = Int | Bool | NullPtr | IntPtr | BoolPtr | Error

// Convert 'CType' into 'Typ'.
let ctypeToTyp (ctype: CType) : Typ =
  match ctype with
  | CInt -> Int
  | CBool -> Bool
  | CIntPtr -> IntPtr
  | CBoolPtr -> BoolPtr
  
// Check ctype == exp type
let type_match type1 type2 : bool =
  match (type1, type2) with
  | (Int, Int) -> true
  | (Bool, Bool) -> true
  | (IntPtr, IntPtr) -> true
  | (IntPtr, NullPtr) -> true
  | (BoolPtr, BoolPtr) -> true
  | (BoolPtr, NullPtr) -> true
  | _ -> false
  
let ptr_match type1 type2 : bool =
  match (type1, type2) with
  | (IntPtr, Int) -> true
  | (BoolPtr, Bool) -> true
  | _ -> false
  
let equal_match type1 type2 : Typ =
  match (type1, type2) with
  | (Int, Int) -> Bool
  | (Bool, Bool) -> Bool
  | (IntPtr, IntPtr) -> Bool
  | (IntPtr, NullPtr) -> Bool
  | (NullPtr, IntPtr) -> Bool
  | (BoolPtr, BoolPtr) -> Bool
  | (BoolPtr, NullPtr) -> Bool
  | (NullPtr, BoolPtr) -> Bool
  | (NullPtr, NullPtr) -> Bool
  | _ -> Error

// Check expression 'e' and return its type. If the type of expression cannot be
// decided due to some semantic error, return 'Error' as its type.
let rec checkExp (symTab: SymbolTable) (e: Exp) : Typ = 
  match e with
  | Null -> NullPtr
  | Num _ -> Int
  | Boolean _ -> Bool
  | Var id ->
    let c = Map.containsKey id symTab
    if c then ctypeToTyp(Map.find id symTab)     
    else Error
  | Deref id ->
    let tmp = ctypeToTyp(Map.find id symTab)
    if tmp = IntPtr then Int
    elif tmp = BoolPtr then Bool
    else Error
  | AddrOf id ->
    let tmp = ctypeToTyp(Map.find id symTab)
    if tmp = Int then IntPtr
    elif tmp = Bool then BoolPtr
    else Error
  | Neg exp ->
    let tmp = checkExp symTab exp
    if tmp = Int then Int else Error
  | Add (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Int else Error
  | Sub (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Int else Error
  | Mul (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Int else Error
  | Div (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Int else Error
  | Equal (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    equal_match t1 t2
  | NotEq (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    equal_match t1 t2
  | LessEq (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Bool else Error
  | LessThan (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Bool else Error
  | GreaterEq (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Bool else Error
  | GreaterThan (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Int then Bool else Error
  | And (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Bool then Bool else Error
  | Or (exp1, exp2) ->
    let t1 = checkExp symTab exp1
    let t2 = checkExp symTab exp2
    if t1 = t2 && t1 = Bool then Bool else Error
  | Not exp ->
    let t1 = checkExp symTab exp
    if t1 = Bool then Bool else Error

// Check statement 'stmt' and return a pair of (1) list of line numbers that
// contain semantic errors, and (2) symbol table updated by 'stmt'.
let rec checkStmt (symTab: SymbolTable) (retTyp: CType) (stmt: Stmt) =
  match stmt with 
  | Declare (line, ctyp, id) ->  //int x; 참고로 int x; bool x; 중복 이름 다른 변수는 같은 scope에서 안 준다고 하셨음.
    ([], Map.add id ctyp symTab) 
  | Define (line, ctyp, id, exp) -> //int x = 0;
    if type_match (ctypeToTyp(ctyp)) (checkExp symTab exp) then ([], Map.add id ctyp symTab)
    else ([line], Map.add id ctyp symTab)
  | Assign (line, id, exp) -> //x = 10;
    let already_declare = Map.containsKey id symTab     //x가 선언 되었는지 체크
    if already_declare then
      if type_match (ctypeToTyp(Map.find id symTab)) (checkExp symTab exp) then ([], symTab)
      else ([line], symTab)
    else ([line], symTab) //오류임. 선언안 된 변수 사용
  | PtrUpdate (line, id, exp) -> //*x = 10;
    let already_declare = Map.containsKey id symTab
    if already_declare then
      if ptr_match (ctypeToTyp(Map.find id symTab)) (checkExp symTab exp) then ([], symTab)
      else ([line], symTab)
    else ([line], symTab) //오류임. 선언안 된 변수 사용
  | Return (line, exp) ->        //return 0;
    if type_match (ctypeToTyp(retTyp)) (checkExp symTab exp) then ([], symTab)
    else ([line], symTab)
  | If (line, exp, if_stmt_list, else_stmt_list) ->
    let exp_op = checkExp symTab exp
    let if_ok = checkStmts symTab retTyp if_stmt_list
    let else_ok = checkStmts symTab retTyp else_stmt_list
    if if_ok = [] && else_ok = [] then
      if exp_op = Error then ([line], symTab)
      else ([], symTab)
    else
      if exp_op = Error then ([line] @ if_ok @ else_ok, symTab)
      else (if_ok @ else_ok, symTab)
  | While (line, exp, stmt_list) ->
    let exp_op = checkExp symTab exp
    let st_ok = checkStmts symTab retTyp stmt_list
    if st_ok = [] then
      if exp_op = Error then ([line], symTab)
      else ([], symTab)
    else
      if exp_op = Error then ([line] @ st_ok, symTab)
      else  (st_ok, symTab)
// Check the statement list and return the line numbers of semantic errors. Note
// that 'checkStmt' and 'checkStmts' are mutually-recursive (they can call each
// other). This function design will make your code more concise.
and checkStmts symTab (retTyp: CType) (stmts: Stmt list): LineNo list =
  match stmts with
  | [] -> []
  | head :: tail ->
    let (line_list, new_symTab) = checkStmt symTab retTyp head
    (line_list @ checkStmts new_symTab retTyp tail)
     
// Record the type of arguments to the symbol table.
let rec collectArgTypes argDecls symTab =
  match argDecls with //argDecls = CType * Identifier: 함수 선언부에 변수 선언하는 곳
  | [] -> symTab
  | (ctyp, id) :: tail -> collectArgTypes tail (Map.add id ctyp symTab) 

// Check the program and return the line numbers of semantic errors.
let run (prog: Program) : LineNo list =
  let (retTyp, _, args, stmts) = prog //CType * Identifier * ArgDecl list * Stmt list
  let symTab = collectArgTypes args Map.empty
  let errorLines = checkStmts symTab retTyp stmts
  List.sort (List.distinct errorLines) // Remove duplicate entries and sort in ascending order.