module Optimize

open CFG.CFG
open IR
open CFG
open DFA

module ConstantFolding =
  let foldConstant instr =
    match instr with
    | UnOp (r, NegOp, Imm x) -> (true, Set (r, Imm (-x)))
    | UnOp (r, NotOp, Imm x) -> (true, Set (r, Imm (if x = 0 then 1 else 0)))
    | BinOp (r, AddOp, Imm x, Imm y) -> (true, Set (r, Imm (x + y)))
    | BinOp (r, AddOp, Imm 0, y) -> (true, Set (r, y))
    | BinOp (r, AddOp, x, Imm 0) -> (true, Set (r, x))
    | BinOp (r, SubOp, Imm x, Imm y) -> (true, Set (r, Imm (x - y)))
    // | BinOp (r, SubOp, Imm 0, y) -> (true, Set (r, y)) //UnOp도 필요해서 복잡해지니까 걍 생략..
    | BinOp (r, SubOp, x, Imm 0) -> (true, Set (r, x))
    | BinOp (r, MulOp, Imm x, Imm y) -> (true, Set (r, Imm (x * y)))
    | BinOp (r, MulOp, Imm 1, y) -> (true, Set (r, y))
    | BinOp (r, MulOp, x, Imm 1) -> (true, Set (r, x))
    | BinOp (r, MulOp, Imm 0, _) -> (true, Set (r, Imm 0))
    | BinOp (r, MulOp, _, Imm 0) -> (true, Set (r, Imm 0))
    | BinOp (r, SubOp, x, y) -> // 이거는 Constant Folding이라고 보긴 힘들지만 코드 형식이 비슷해서 하는 최적화들
        if x = y then (true, Set (r, Imm 0))
        else (false, instr)
    | BinOp (r, DivOp, Imm x, Imm y) ->
        match y with
        | 0 -> (false, instr)
        | _ -> (true, Set (r, Imm (x / y)))
    | BinOp (r, DivOp, x, Imm 1) -> (true, Set (r, x))
    | BinOp (r, EqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x = y then 1 else 0)))
    | BinOp (r, EqOp, x, y) ->
        if x = y then (true, Set (r, Imm 1))
        else (false, instr)
    | BinOp (r, NeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <> y then 1 else 0)))
    | BinOp (r, NeqOp, x, y) ->
        if x = y then (true, Set (r, Imm 0))
        else (false, instr)
    | BinOp (r, LeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <= y then 1 else 0)))
    | BinOp (r, LeqOp, x, y) ->
        if x = y then (true, Set (r, Imm 1))
        else (false, instr)
    | BinOp (r, LtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x < y then 1 else 0)))
    | BinOp (r, LtOp, x, y) ->
        if x = y then (true, Set (r, Imm 0))
        else (false, instr)
    | BinOp (r, GeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x >= y then 1 else 0)))
    | BinOp (r, GeqOp, x, y) ->
        if x = y then (true, Set (r, Imm 1))
        else (false, instr)
    | BinOp (r, GtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x > y then 1 else 0)))
    | BinOp (r, GtOp, x, y) ->
        if x = y then (true, Set (r, Imm 0))
        else (false, instr)
    | GotoIf (Imm x, l) -> (true, if x <> 0 then Goto l else Label "trashfolding")
    | GotoIfNot (Imm x, l) -> (true, if x <> 0 then Label "trashfolding" else Goto l)
    | _ -> (false, instr)

  let run instrs =
    let results = List.map foldConstant instrs
    let flags, instrs = List.unzip results
    let isOptimized = List.contains true flags
    (isOptimized, instrs)
    
    
module ConstantPropagation =
    let run instrs =
        let cfg = CFG.make instrs
        let rdMap = RDAnalysis.run cfg
        let NodeList = getAllNodes cfg
        let mutable opt = false 
        let mutable retlist = []
        for node in NodeList do
            let instr = getInstr node cfg
            let rd_in_node = rdMap[node]
            let can o: _ =
                let mutable can = true
                let related_defs =
                      rd_in_node |> Set.filter (fun d -> match d with
                                                          | Set(r, _) when Reg r = o -> true                                                          
                                                          | UnOp(r, _, _) when Reg r = o ->
                                                              can <- false
                                                              true
                                                          | BinOp(r, _, _, _) when Reg r = o ->
                                                              can <- false
                                                              true
                                                          | Load(r, _) when Reg r = o ->
                                                              can <- false
                                                              true    
                                                          | _ -> false)
                match Set.toList related_defs with
                | [Set(_, Imm c)] when can -> Some c
                | _ -> None
                
            match instr with
            | Set(r, o) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- Set(r, Imm c) :: retlist
                | None -> retlist <- instr :: retlist
            | UnOp(r, un, o) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- UnOp(r, un, Imm c) :: retlist
                | None -> retlist <- instr :: retlist
            | BinOp(r, op, o1, o2) ->
                match can o1, can o2 with
                | Some c1, Some c2 ->
                    opt <- true
                    retlist <- BinOp(r, op, Imm c1, Imm c2) :: retlist
                | Some c1, None ->
                    opt <- true
                    retlist <- BinOp(r, op, Imm c1, o2) :: retlist
                | None, Some c2 ->
                    opt <- true
                    retlist <- BinOp(r, op, o1, Imm c2) :: retlist 
                | None, None -> retlist <- instr :: retlist
            | Store(o, r) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- Store(Imm c, r) :: retlist
                | None -> retlist <- instr :: retlist
            | GotoIf(o, l) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- GotoIf(Imm c, l) :: retlist
                | None -> retlist <- instr :: retlist
            | GotoIfNot(o, l) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- GotoIfNot(Imm c, l) :: retlist
                | None -> retlist <- instr :: retlist
            | Ret o ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- Ret(Imm c) :: retlist
                | None -> retlist <- instr :: retlist
            | _ -> retlist <- instr :: retlist
        (opt, List.rev retlist)

    
module Mem2Reg =
  let run instrs =
    let trash_above = "trash_above"
    let trash_below = "trash_below"
    let label_set =
                    instrs 
                    |> List.filter (fun instr ->
                        match instr with
                        | Label c -> c[0] = '%'
                        | _ -> false
                        )
                    |> Set.ofList
    let can index instr instrs =
        match instr with
        | LocalAlloc (reg, _) ->
            if index - 1 < 0 || index + 1 >= List.length instrs then None
            else
                match (List.tryItem (index - 1) instrs, List.tryItem (index + 1) instrs) with
                | Some (Label a), Some (Label b) when a = trash_above && b = trash_below ->
                    if not (Set.contains (Label reg) label_set) then Some reg
                    else None
                | _ -> None
        | _ -> None
    

    let del_set =
        instrs
        |> List.fold (fun (acc, index) instr ->
            match can index instr instrs with
            | Some ret -> (Set.add ret acc, index + 1)
            | None -> (acc, index + 1)  
        ) (Set.empty, 0)
        |> fst

    
    if Set.count del_set = 0 then (false, instrs)
    else
        let fix_instrs (instrs: Instr list) (del_set: Set<Register>) =
            instrs
            |> List.map (fun x ->
                match x with
                | LocalAlloc(reg, _) when Set.contains reg del_set -> None  // LocalAlloc 제거
                | Store(o, reg) when Set.contains reg del_set -> Some(Set(reg, o))  // Store 변환
                | Load(r1, reg) when Set.contains reg del_set -> Some(Set(r1, Reg reg))  // Load 변환
                | _ -> Some x
            )
            |> List.choose id
        (true, fix_instrs instrs del_set)

module DeadCodeElimination =
  let run instrs =
     let cfg = CFG.make instrs
     let laSet = LAAnalysis.run cfg    
     let NodeList = List.rev (getAllNodes cfg)
     
     let mutable opt = false
     let mutable retlist = []
     for node in NodeList do
        let instr = getInstr node cfg
        let la_out_node = laSet[node]
        match instr with
        | Set(r, _) ->
            if Set.contains r la_out_node then retlist <- instr :: retlist
            else opt <- true
        | LocalAlloc(r, _) ->
            if Set.contains r la_out_node then retlist <- instr :: retlist
            else opt <- true
        | UnOp(r, _, _) ->
            if Set.contains r la_out_node then retlist <- instr :: retlist
            else opt <- true
        | BinOp(r, _, _, _) ->
            if Set.contains r la_out_node then retlist <- instr :: retlist
            else opt <- true
        | Load(r, _) ->
            if Set.contains r la_out_node then retlist <- instr :: retlist
            else opt <- true
        | _ -> retlist <- instr :: retlist
     (opt, retlist)

module CopyPropagation =
  let run instrs =
    let cfg = CFG.make instrs
    let AESet = AEAnalysis.run cfg
    let mutable opt = false
    let NodeList = getAllNodes cfg
    let mutable retlist = []
    let mutable U = Set.empty<Instr>
    for node in NodeList do
        let instr = getInstr node cfg
        U <- Set.add instr U
    
    for node in NodeList do
            let instr = getInstr node cfg
            let ae_in_node = AESet[node]
            let get_reg reg : _ =
                let filtered_set =
                    ae_in_node 
                    |> Set.filter (fun instr ->
                        match instr with
                        | Set(x, _) -> reg = Reg x
                        | _ -> false
                        )
                if Set.count filtered_set = 1 then
                    match Set.toList filtered_set with
                    | [Set (x, y)] -> Some y
                    | _ -> None
                else None
            
            match instr with
            | Set (r, o) -> // r = o
                let REG = get_reg o
                match REG with
                | Some y ->
                    opt <- true
                    retlist <- Set(r, y) :: retlist
                | None -> retlist <- instr :: retlist
            | UnOp (r, uop, o) ->
                let REG = get_reg o
                match REG with
                | Some y ->
                    opt <- true
                    retlist <- UnOp(r, uop, y) :: retlist
                | None -> retlist <- instr :: retlist
            | BinOp (r, bop, o1, o2) ->
                let REG1 = get_reg o1
                let REG2 = get_reg o2
                match (REG1, REG2) with
                | Some y1, Some y2 ->
                    opt <- true
                    retlist <- BinOp(r, bop, y1, y2) :: retlist
                | Some y1, None ->
                    opt <- true
                    retlist <- BinOp(r, bop, y1, o2) :: retlist
                | None, Some y2 ->
                    opt <- true
                    retlist <- BinOp(r, bop, o1, y2) :: retlist
                | _ -> retlist <- instr :: retlist
            | GotoIf (o, l) ->
                let REG = get_reg o
                match REG with
                | Some y ->
                    opt <- true
                    retlist <- GotoIf(y, l) :: retlist
                | None -> retlist <- instr :: retlist 
            | GotoIfNot (o, l) ->
                let REG = get_reg o
                match REG with
                | Some y ->
                    opt <- true
                    retlist <- GotoIfNot(y, l) :: retlist
                | None -> retlist <- instr :: retlist
            | Ret o ->
                let REG = get_reg o
                match REG with
                | Some y ->
                    opt <- true
                    retlist <- Ret y :: retlist
                | None -> retlist <- instr :: retlist
            | _ -> retlist <- instr :: retlist
    (opt, List.rev retlist)
    
module CommonSubexpressionElimination =
    let run instrs =
        let cfg = CFG.make instrs
        let AESet = AEAnalysis.run cfg
        let NodeList = getAllNodes cfg
        let mutable opt = false
        let mutable retlist = []
        let mutable U = Set.empty<Instr>
        for node in NodeList do
            let instr = getInstr node cfg
            U <- Set.add instr U
            
        for node in NodeList do
            let instr = getInstr node cfg
            let ae_in_node = AESet[node]     
            
            match instr with
            | Load (r1, r2) ->
                let get_same_exp =
                    ae_in_node 
                    |> Set.filter (fun instr ->
                        match instr with
                        | Load(sr1, sr2) -> r2 = sr2
                        | _ -> false
                        )
                if Set.count get_same_exp = 1 then 
                    match Set.toList get_same_exp with
                    | [Load (x, y)] ->
                        opt <- true
                        retlist <- Set(r1, Reg x) :: retlist
                    | _ -> retlist <- instr :: retlist
                else retlist <- instr :: retlist
            | UnOp(r, un, o) ->
                let get_same_exp = 
                    ae_in_node 
                    |> Set.filter (fun instr ->
                        match instr with
                        | UnOp(sr, sun, so) -> sun = un && so = o
                        | _ -> false
                        )
                if Set.count get_same_exp = 1 then 
                    match Set.toList get_same_exp with
                    | [UnOp(sr, _, _)] ->
                        opt <- true
                        retlist <- Set(r, Reg sr) :: retlist
                    | _ -> retlist <- instr :: retlist
                else retlist <- instr :: retlist
            | BinOp(r, bin, o1, o2) ->
                let get_same_exp = 
                    ae_in_node 
                    |> Set.filter (fun instr ->
                        match instr with
                        | BinOp(sr, sbin, so1, so2) -> sbin = bin && so1 = o1 && so2 = o2
                        | _ -> false
                        )
                if Set.count get_same_exp = 1 then
                    match Set.toList get_same_exp with
                    | [BinOp(sr, _, _, _)] ->
                        opt <- true
                        retlist <- Set(r, Reg sr) :: retlist
                    | _ -> retlist <- instr :: retlist
                else retlist <- instr :: retlist
            | _ -> retlist <- instr :: retlist
        (opt, List.rev retlist)

   
module MyDel =
    // 1 gotolabel l이 있고
    // 2 그 명령어 뒤쪽에 l이 있고
    // 3 사이에 label이 없으면 (trash label은 있어도 됨)
    // 4 1 ~ 2 사이 instruction 삭제 가능
    let run instrs =
        let arr = List.toArray instrs
        let mutable lidx = -1
        let mutable ridx = -1
        for i in 0 .. ((Array.length arr) - 1) do
            match arr.[i] with
            | Goto(l1) ->
                let mutable can = true
                let mutable finished = false
                for j in (i + 1) .. ((List.length instrs) - 1) do
                    if can = false || finished then ()
                    else
                        match arr.[j] with
                        | Label l2 ->
                            if (l1 = l2) then
                                lidx <- i
                                ridx <- j
                                finished <- true
                            else
                                match l2 with
                                | "trash_above" | "trash_below" | "trashfolding" -> ()
                                | _ -> can <- false
                        | _ -> ()
            | _ -> ()
        if lidx <> -1 && ridx <> -1 then
            let mutable retlist = []
            for i in 0 .. ((Array.length arr) - 1) do
                if lidx <= i && i <=ridx then ()
                else retlist <- arr.[i] :: retlist
            (true, List.rev retlist)
        else (false, Array.toList arr)
               

// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  
  // Mem2Reg
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let m2r, instrs = Mem2Reg.run instrs
  
  // CopyPropagation
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let copy_prop, instrs = CopyPropagation.run instrs
  
  // ConstantFolding
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let cons_fold, instrs = ConstantFolding.run instrs
  
  // ConstantPropagation
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let cons_prop, instrs = ConstantPropagation.run instrs
 
  // CommonSubexpressionElimination
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let cse, instrs = CommonSubexpressionElimination.run instrs
  
  // DeadCodeElimination
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let dce, instrs = DeadCodeElimination.run instrs
  
  // 효과 없는 듯..
  // let my_del, instrs = MyDel.run instrs
  
  // if m2r then printf "m2r "
  // if cons_fold then printf "cons_fold "
  // if cons_prop then printf "cons_prop "
  // if copy_prop then printf "copy_prop "
  // if cse then printf "cse "
  // if dce then printf "dce "
  // if my_del then printf "my_del "
  // printfn ""
  if
      m2r ||
      cons_fold ||
      cons_prop || 
      copy_prop ||
      cse ||
      dce ||
      // my_del ||
      false
      then
          optimizeLoop instrs else instrs
    
// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  (fname, args, optimizeLoop instrs)