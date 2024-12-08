open Program
open Error

(* Our symbol table will be a mapping from 'string' to 'ctype_entry'. *)
type ctype_entry =
  | VarType of ctype
  | FuncType of ctype * ctype list (* return type * argument type list *)

(* Define a module for symbol table *)
module SymbolMap = Map.Make(String)

(* During the semantic analysis, this type can be helpful. Why do we need this
 * even though 'ctype' is already defined? If you encounter a wrong expression
 * during the semantic analysis (for example "1 + true"), you cannot decide its
 * type but still may have to return something. *)
type typ = Void | Int | Bool | Unknown

let ctyp_to_typ ctyp =
  match ctyp with
  | CVoid -> Void
  | CInt -> Int
  | CBool -> Bool

let typ_to_ctyp ctyp =
  match ctyp with
  | Void -> CVoid
  | Int -> CInt
  | Bool -> CBool
  | Unknown -> (* Raise exception *)
      failwith "Not allowed (You should not call this in such situation)"

(* Record the type of variables into the symbol table *)
let rec collect_vars decls sym_tab =
  match decls with
  | [] -> sym_tab
  | head_decl :: tail_decls ->
      let (ctyp, vname) = head_decl in
      let sym_tab = SymbolMap.add vname (VarType ctyp) sym_tab in
      collect_vars tail_decls sym_tab

(* Record the type of functions into the symbol table *)
let rec collect_functions funcs sym_tab =
  (* TODO *)
  match funcs with
  | [] -> sym_tab
  | head_f :: tail_fs ->
    let (fname, ret_typ, args, _) = head_f in
    let sym_tab = SymbolMap.add fname (FuncType (ret_typ, List.map fst args)) sym_tab in
    collect_functions tail_fs sym_tab
    
(* Check expression 'e' and return detected semantic errors, along with the
 * decided type of 'e'. If the type of expression cannot be decided due to
 * semantic error, return 'Unknown' as its type. *)
let rec check_exp sym_tab e =
  match e with
  | ConstBool b -> ([], Bool)
  | ConstInt i -> ([], Int)
  (* TODO: Fill in the remaining cases below *)
  | Var vname ->
    if (SymbolMap.mem vname sym_tab) = true then
    (match SymbolMap.find vname sym_tab with
     | VarType typ -> ([], ctyp_to_typ typ)
     | FuncType (_,_) -> ([CallingVariable vname], Unknown))
    else ([UndefinedName vname], Unknown)
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) ->
    let (errors1, type1) = check_exp sym_tab e1 in
    let (errors2, type2) = check_exp sym_tab e2 in
    if type1 = Int && type2 = Int then
      (errors1 @ errors2, Int)
    else
      ([OperandMismatch], Unknown)
  | Neg exp ->
    let (errors, typ) = check_exp sym_tab exp in
    if typ = Int then
      (errors, Int)
    else
      ([OperandMismatch], Unknown)
  | Equal (e1, e2) | NotEq (e1, e2) -> 
    let (errors1, type1) = check_exp sym_tab e1 in
    let (errors2, type2) = check_exp sym_tab e2 in
    if type1 = type2 then
      (errors1 @ errors2, Bool)
    else
      ([OperandMismatch], Unknown)
  | LessEq (e1, e2) | LessThan (e1, e2) | GreaterEq(e1, e2) | GreaterThan(e1, e2) ->
    let (errors1, type1) = check_exp sym_tab e1 in
    let (errors2, type2) = check_exp sym_tab e2 in
    if type1=Int && type2=Int then
      (errors1 @ errors2, Bool)
    else
      ([OperandMismatch], Unknown)
  | And (e1, e2) | Or (e1, e2) ->
    let (errors1, type1) = check_exp sym_tab e1 in
    let (errors2, type2) = check_exp sym_tab e2 in
    if type1 = Bool && type2 = Bool then
      (errors1 @ errors2, Bool)
    else
      ([OperandMismatch], Unknown)
  | Not e1 ->
    let (errors, typ) = check_exp sym_tab e1 in
    if typ = Bool then
      (errors, Bool)
    else
      ([OperandMismatch], Unknown)
  | CallExp (fname, exps) ->
    if (SymbolMap.mem fname sym_tab) = true then
      (match SymbolMap.find fname sym_tab with
      | FuncType(ret_typ, arg_typ) ->
        let (es,_) = check_arg sym_tab exps arg_typ in
        (es, ctyp_to_typ ret_typ)
      | VarType(_) -> ([CallingVariable fname], Unknown))
    else ([UndefinedName fname], Unknown)

and check_arg sym_tab exps arg_typ = 
  match (exps, arg_typ) with
  | [], [] -> ([], [])
  | head_exp::tail_exps, head_art::tail_arts ->
    let(e1, art) = check_exp sym_tab head_exp in
    let(es, _) = check_arg sym_tab tail_exps tail_arts in
    if art = ctyp_to_typ head_art then
      (es, [])
    else
      ([ArgTypeMismatch(head_art, typ_to_ctyp art)] @ es, [])
  | [], _ | _, [] -> ([ArgNumMismatch], [])

(******************************************************************
 * And of course, you will need many more functions between here. *
 * ****************************************************************)
let rec check_stmts sym_tab stmts ret_typ =
  match stmts with
  | [] -> ([], sym_tab)
  | head_stmt :: tail_stmts ->
    let (head_error, t1) = check_stmt sym_tab ret_typ head_stmt in
    let (tail_errors, t2) = check_stmts t1 tail_stmts ret_typ in
    (head_error @ tail_errors, t2)

and check_stmt sym_tab ret_typ stmt =
  match stmt with
  | LocalDecl (t, vname) -> 
    if SymbolMap.mem vname sym_tab 
    then 
      let t1 = SymbolMap.remove vname sym_tab in
      let t2 = SymbolMap.add vname (VarType t) t1 in
      ([], t2)
    else
      let t1 = SymbolMap.add vname (VarType t) sym_tab in
      ([], t1)
  | Assign (vname, e) -> 
    if (SymbolMap.mem vname sym_tab) = true then
    (match SymbolMap.find vname sym_tab with
    | (VarType ctype) -> 
      let (errors, typ) = check_exp sym_tab e in
      if errors = [] 
      then 
        let error = (if ctyp_to_typ ctype <> typ then
          [AssignMismatch (ctype, typ_to_ctyp typ)]
        else []) in
        (errors @ error, sym_tab)
      else (errors, sym_tab)
    | FuncType(_, _) ->([UsingFunctionAsVar vname], sym_tab))
    else ([UndefinedName vname], sym_tab)
  | Call (fname, exps) -> 
    if SymbolMap.mem fname sym_tab = true
    then (match SymbolMap.find fname sym_tab with
      | FuncType(_, arg_typ) ->
        let (errors, _) = check_arg sym_tab exps arg_typ in
        (errors, sym_tab)
      | VarType(_) -> ([CallingVariable fname], sym_tab))
    else ([UndefinedName fname], sym_tab)
  | Return -> 
    if ret_typ = Void then ([], sym_tab) else ([ReturnMismatch (typ_to_ctyp ret_typ, CVoid)], sym_tab)
  | ReturnValue e -> 
    let (errors, typ) = check_exp sym_tab e in
    if errors = [] then
      if ret_typ = typ then (errors @ [], sym_tab) else (errors @ [ReturnMismatch (typ_to_ctyp ret_typ, typ_to_ctyp typ)], sym_tab)
    else (errors, sym_tab)
  | If (e, stmts1, stmts2) -> 
    let (_, typ) = check_exp sym_tab e in
    let (errors1, _) = check_stmts sym_tab stmts1 ret_typ in
    let (errors2, _) = check_stmts sym_tab stmts2 ret_typ in
    let errors3 = if typ = Bool then [] else [OperandMismatch] in
    (errors3 @ errors2 @ errors1, sym_tab)
  | While (e, stmts) -> 
    let (errors1, typ) = check_exp sym_tab e in
    let (errors2, _) = check_stmts sym_tab stmts ret_typ in
    let errors3 = if typ = Bool then [] else [OperandMismatch] in
    (errors3 @ errors2 @ errors1, sym_tab)
    
(* Check functions and return detected semantic errors. *)
let rec check_functions sym_tab funcs =
  match funcs with
  | [] -> []
  | head_func :: tail_funcs ->
    let (fname, ret_typ, args, stmts) = head_func in
    let setted_table = set_table sym_tab args in
    let (head_error, _) = check_stmts setted_table stmts (ctyp_to_typ ret_typ) in
    let tail_errors = check_functions sym_tab tail_funcs in
    head_error @ tail_errors

and set_table sym_tab args =
  match args with
  | [] -> sym_tab
  | head_arg :: tail_args ->
    let (arg_typ, arg) = head_arg in
    if SymbolMap.mem arg sym_tab = true then
      let t1 = SymbolMap.remove arg sym_tab in
      let t2 = SymbolMap.add arg (VarType arg_typ) t1 in
      let t3 = set_table t2 tail_args in
      set_table t3 tail_args
    else
      let t1 = SymbolMap.add arg (VarType arg_typ) sym_tab in
      let t2 = set_table t1 tail_args in
      set_table t2 tail_args

(* Check a program and return detected semantic errors. *)
let run (p: program) : error list =
  let (gdecls, funcs) = p in
  let sym_tab = collect_vars gdecls SymbolMap.empty in
  let sym_tab = collect_functions funcs sym_tab in
  (* At this point, 'sym_tab' must contain global variables & functions *)
  check_functions sym_tab funcs