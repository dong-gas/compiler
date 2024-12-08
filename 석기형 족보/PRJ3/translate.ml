open Program
open Ir
open Helper

(* The module for symbol table. Carefully think about what should be stored in
 * the symbol table for this IR translation phase. *)
module SymbolMap = Map.Make(String)

(* Let's assume that boolean is 1-byte and integer is 4-byte. *)
let sizeof ctyp =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

let rec extract_names args =
  match args with
  | [] -> []
  | (arg_typ, arg_name) :: tail_args -> arg_name :: extract_names tail_args

let rec trans_exp exp sym_tab v =
  match exp with
  | ConstBool b ->
    (* let reg = create_register_name() in *)
    (* ([Set(reg, ImmBool b)], reg) *)
    if SymbolMap.mem v sym_tab = true then
      (* let addr = SymbolMap.find vname sym_tab in
      let reg = create_register_name() in
      ([Load(reg, addr)], reg) *)
      let reg = SymbolMap.find v sym_tab in
      ([Set(reg, ImmBool b)], reg)
    else  
      let reg = create_register_name() in
      ([Set(reg, ImmBool b)], reg)
  | ConstInt i ->
    (* let reg = create_register_name() in *)
    (* ([Set(reg, ImmInt i)], reg) *)
    if SymbolMap.mem v sym_tab = true then
      let reg = SymbolMap.find v sym_tab in
      ([Set(reg, ImmInt i)], reg)
    else  
      let reg = create_register_name() in
      ([Set(reg, ImmInt i)], reg)
  | Var vname ->
    if SymbolMap.mem vname sym_tab = true then
      (* let addr = SymbolMap.find vname sym_tab in
      let reg = create_register_name() in
      ([Load(reg, addr)], reg) *)
      let reg = SymbolMap.find vname sym_tab in
      ([], reg)
    else  
      let reg = create_register_name() in
      ([failwith("Not found: " ^ vname)], reg)
  | Arr (vname, e_idx) ->
    let (instlist_e, reg_e) = trans_exp e_idx sym_tab v in
    if SymbolMap.mem vname sym_tab = true then
      let addr = SymbolMap.find vname sym_tab in
      let addr_reg = create_register_name() in
      let reg = create_register_name() in
      (instlist_e @ [
        BinOp(addr_reg, AddOp, Reg addr, Reg reg_e);
        Load(reg, addr_reg)
      ], reg)
    else
      let reg = create_register_name() in
      (failwith("Not found: " ^ vname), reg)
  | Add (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, AddOp, Reg reg_e1, Reg reg_e2)], reg)
  | Sub (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, SubOp, Reg reg_e1, Reg reg_e2)], reg)
  | Mul (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, MulOp, Reg reg_e1, Reg reg_e2)], reg)
  | Div (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, DivOp, Reg reg_e1, Reg reg_e2)], reg)
  | Neg e ->
    let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e @ [UnOp(reg, NegOp, Reg reg_e)], reg)
  | Equal (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, EqOp, Reg reg_e1, Reg reg_e2)], reg)
  | NotEq (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, NeqOp, Reg reg_e1, Reg reg_e2)], reg)
  | LessEq (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, LeqOp, Reg reg_e1, Reg reg_e2)], reg)
  | LessThan (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, LtOp, Reg reg_e1, Reg reg_e2)], reg)
  | GreaterEq (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, GeqOp, Reg reg_e1, Reg reg_e2)], reg)
  | GreaterThan (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e1 @ instlist_e2 @ [BinOp(reg, GtOp, Reg reg_e1, Reg reg_e2)], reg)
  | And (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let label_true = create_label() in
    let label_false = create_label() in
    let reg = create_register_name() in
    (instlist_e1 @ 
      [GotoIfNot(reg_e1, label_false)] @
      instlist_e2 @
      [GotoIfNot(reg_e2, label_false); 
      Set(reg, ImmBool true); 
      Goto(label_true);
      Label(label_false);
      Set(reg, ImmBool false);
      Label(label_true)
      ], reg)
  | Or (e1, e2) ->
    let (instlist_e1, reg_e1) = trans_exp e1 sym_tab "Dummy" in
    let (instlist_e2, reg_e2) = trans_exp e2 sym_tab "Dummy" in
    let label_true = create_label() in
    let label_false = create_label() in
    let reg = create_register_name() in
    (instlist_e1 @ [
      GotoIf(reg_e1, label_true)] @
      instlist_e2 @ 
      [GotoIf(reg_e2, label_true); 
      Set(reg, ImmBool false); 
      Goto(label_false);
      Label(label_true);
      Set(reg, ImmBool true);
      Label(label_false)
      ], reg)
  | Not e ->
    let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
    let reg = create_register_name() in
    (instlist_e @ [UnOp(reg, NotOp, Reg reg_e)], reg)

let rec trans_stmt stmts sym_tab =
  match stmts with
  | [] -> []
  | head_stmt :: tail_stmts ->
    let (instlist_stmt, sym_tab) =
      (match head_stmt with
      | LocalDecl decl ->
        let (typ, vname) = decl in
        let reg = create_register_name() in
        let sym_tab = SymbolMap.add vname reg sym_tab in
        let typeinst = 
          match typ with
          | CInt ->
            [LocalAlloc(reg, sizeof CInt)]
          | CBool ->
            [LocalAlloc(reg, sizeof CBool)]
          | CIntArr n ->
            [LocalAlloc(reg, sizeof(CIntArr n))]
          | CBoolArr n ->
            [LocalAlloc(reg, sizeof(CBoolArr n))]
          in
        (typeinst, sym_tab)
      | Assign (lv, e) ->
        (match lv with
        | LVar v ->
          if SymbolMap.mem v sym_tab = true then
            let reg = SymbolMap.find v sym_tab in
            let (instlist_e, reg_e) = trans_exp e sym_tab v in
            if reg = reg_e then
              (instlist_e, sym_tab)
            else
              (instlist_e @ [Copy(reg_e, reg)], sym_tab)
          else
            let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
            (instlist_e @ failwith("Not found: " ^ v), sym_tab)
        | LArr (v, ea) ->
          let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
          let (instlist_ea, reg_ea) = trans_exp ea sym_tab "Dummy" in
          let new_reg = create_register_name() in
          if SymbolMap.mem v sym_tab = true then
            let reg = SymbolMap.find v sym_tab in
            (instlist_e @ instlist_ea @ 
            [BinOp(new_reg, AddOp, Reg reg, Reg reg_ea);
            Store(Reg reg_e, new_reg)], sym_tab)
          else
            (instlist_e @ instlist_ea @ failwith("Not found: " ^ v), sym_tab))
      | ReturnValue e ->
        let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
        (instlist_e @ [Ret(Reg reg_e)], sym_tab)
      | If (e, s1, s2) ->
        let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
        let label_true = create_label() in
        let label_false = create_label() in
        let stmt_true = trans_stmt s1 sym_tab in
        let stmt_false = trans_stmt s2 sym_tab in
        (instlist_e @
        [GotoIfNot(reg_e, label_false)] @
        stmt_true @
        [Goto(label_true);
        Label label_false] @
        stmt_false @
        [Label label_true], sym_tab)
      | While (e, s) ->
        let (instlist_e, reg_e) = trans_exp e sym_tab "Dummy" in
        let label_true = create_label() in
        let label_false = create_label() in
        let instlist_while = trans_stmt s sym_tab in
        (instlist_e @
        [Label label_true;
        GotoIfNot(reg_e, label_false)] @
        instlist_while @
        instlist_e @
        [Goto(label_true);
        Label label_false], sym_tab))
  in
  instlist_stmt @ trans_stmt tail_stmts sym_tab
  
let rec trans_args args sym_tab =
  match args with
  | [] -> ([] , sym_tab)
  | (typ, name) :: tail_args ->
    let sym_tab = SymbolMap.add name name sym_tab in
    let (_, sym_tab) = trans_args tail_args sym_tab in
    ([], sym_tab)  
    (* (match typ with
      | CInt ->
        let reg = create_register_name() in
        let sym_tab = SymbolMap.add name reg sym_tab in
        let (instrs, sym_tab) = trans_args tail_args sym_tab in
        ([LocalAlloc(reg, sizeof CInt);
        Store(Reg name, reg);
        Load(reg, reg)] @
        instrs, sym_tab)
      | CBool ->
        let reg = create_register_name() in
        let sym_tab = SymbolMap.add name reg sym_tab in
        let (instrs, sym_tab) = trans_args tail_args sym_tab in
        ([LocalAlloc(reg, sizeof CBool);
        Store(Reg name, reg);
        Load(reg, reg)] @ 
        instrs, sym_tab)
      | CIntArr n -> 
        let reg = create_register_name() in
        let sym_tab = SymbolMap.add name reg sym_tab in
        let (instrs, sym_tab) = trans_args tail_args sym_tab in
        ([LocalAlloc(reg, sizeof(CIntArr n))] @
          instrs, sym_tab)
      | CBoolArr n ->
        let reg = create_register_name() in
        let sym_tab = SymbolMap.add name reg sym_tab in
        let (instrs, sym_tab) = trans_args tail_args sym_tab in
        ([LocalAlloc(reg, sizeof(CBoolArr n))] @
          instrs, sym_tab)) *)

let run (p: program): ir_code =
  let (fname, ret_type, args, stmts) = p in
  let arg_regs = extract_names args in
  let sym_tab = SymbolMap.empty in
  let (args_instrs, sym_tab) = trans_args args sym_tab in
  let instrs = trans_stmt stmts sym_tab in
  (fname, arg_regs, args_instrs @ instrs)
