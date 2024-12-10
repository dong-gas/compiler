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
    | BinOp (r, SubOp, Imm x, Imm y) -> (true, Set (r, Imm (x - y)))
    | BinOp (r, MulOp, Imm x, Imm y) -> (true, Set (r, Imm (x * y)))
    | BinOp (r, DivOp, Imm x, Imm y) -> (true, Set (r, Imm (x / y)))
    | BinOp (r, EqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x = y then 1 else 0)))
    | BinOp (r, NeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <> y then 1 else 0)))
    | BinOp (r, LeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x <= y then 1 else 0)))
    | BinOp (r, LtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x < y then 1 else 0)))
    | BinOp (r, GeqOp, Imm x, Imm y) -> (true, Set (r, Imm (if x >= y then 1 else 0)))
    | BinOp (r, GtOp, Imm x, Imm y) -> (true, Set (r, Imm (if x > y then 1 else 0)))
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
        // printfn "here1"
        let rdMap = RDAnalysis.run cfg // in이 아닌 out set을 가지고 있음 주의...
        let NodeList = getAllNodes cfg
        let rec union_set (s: RDSet) (list: int list) (rd: Map<int, RDSet>) : RDSet =
            match list with
            | [] -> s
            | head :: tail ->
                let ret = Set.union s (Map.find head rd)
                union_set ret tail rd
        let mutable opt = false 
        let mutable retlist = []
        // printfn "here2"
        for node in NodeList do
            let instr = getInstr node cfg
            let pre = getPreds node cfg
            let rd_in_node = union_set Set.empty<Instr> pre rdMap
            let can (o: Operand) : Option<int> =
                // `rd_in_node`에서 `o`와 관련된 정의만 필터링
                let related_defs =
                      rd_in_node |> Set.filter (fun d -> match d with
                                                          | Set(r, _) when Reg r = o -> true
                                                          | _ -> false)
                // 정의된 횟수가 1개이고, 그 값이 상수인지 확인
                match Set.toList related_defs with
                | [Set(_, Imm c)] -> Some c
                | _ -> None
            match instr with
            // o(operand)가 register이면서..
            // rd_in_node라는 set에 그 o(register)가 정의되는 횟수(set만 봐도 됨) 가 1개면.. 바꿀 수 있음
            // 
            // BinOp, UnOp는 folding에서 최적화 되고 나면 다시 돌면서 되겠지
            // Load는 mem2Reg에서 될 듯..
            // 그 register가 상수면 
            
            | Set(r, o) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [Set(r, Imm c)]
                | None ->
                    retlist <- retlist @ [instr]
            | UnOp(r, un, o) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [UnOp(r, un, Imm c)]
                | None ->
                    retlist <- retlist @ [instr]
            | BinOp(r, op, o1, o2) ->
                match can o1, can o2 with
                | Some c1, Some c2 ->
                    opt <- true
                    retlist <- retlist @ [BinOp(r, op, Imm c1, Imm c2)]
                | Some c1, None ->
                    opt <- true
                    retlist <- retlist @ [BinOp(r, op, Imm c1, o2)]
                | None, Some c2 ->
                    opt <- true
                    retlist <- retlist @ [BinOp(r, op, o1, Imm c2)] 
                | _ ->
                    retlist <- retlist @ [instr]
            | Store(o, r) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [Store(Imm c, r)]
                | None ->
                    retlist <- retlist @ [instr]
            | GotoIf(o, l) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [GotoIf(Imm c, l)]
                | None ->
                    retlist <- retlist @ [instr]
            | GotoIfNot(o, l) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [GotoIfNot(Imm c, l)]
                | None ->
                    retlist <- retlist @ [instr]
            | Ret o ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [Ret(Imm c)]
                | None ->
                    retlist <- retlist @ [instr]
            | _ -> retlist <- retlist @ [instr]
        // printfn "here3"
        (opt, retlist)
    
module Mem2Reg =
  let run instrs =
    let cfg = CFG.make instrs
    let can index instr instrs =
        match instr with
        | LocalAlloc (reg, _) ->
            let isLabel i =
                if i < 0 || i >= List.length instrs then false
                else 
                    match List.tryItem i instrs with
                    | Some (Label "trash") -> true
                    | _ -> false
            if (isLabel (index - 2) && isLabel (index - 1) && isLabel (index + 1) && isLabel (index + 2))
                then Some reg else None
        | _ -> None
    
    let mutable R = None
    let mutable x = -1
    List.iteri (fun index instr ->
        let ret = can index instr instrs
        if  ret <> None then
            x <- index
            R <- ret
    ) instrs
    
    if x = -1 then (false, instrs) else
        let replace_store_to_set (lst: Instr List) =
            lst |> List.map (fun x ->
                        match x with
                        | Store(o, reg) ->
                            if Some reg = R then Set (reg, o)
                            else x
                        | _ -> x 
                )
        let replace_load_to_set (lst: Instr list) =
            lst |> List.map (fun x ->
                        match x with
                        | Load(r1, reg) ->
                            match R with
                            | Some r when reg = r -> Set (r1, Reg r)
                            | _ -> x
                        | _ -> x 
                )
        let remove_localAlloc (lst: Instr list) =
            lst |> List.filter (fun x ->
                    match x with
                    | LocalAlloc(reg, _) ->
                        if Some reg = R then false
                        else true
                    | _ -> true
                )
        let retlist = instrs
        let retlist = replace_load_to_set retlist
        let retlist = replace_store_to_set retlist
        let retlist = remove_localAlloc retlist
        (true, retlist)

module DeadCodeElimination =
  let run instrs =
     let cfg = CFG.make instrs
     let laSet = LAAnalysis.run cfg    
     let NodeList = List.rev (getAllNodes cfg)
     let rec union_set (s: LASet) (list: int list) (rd: Map<int, LASet>) : LASet =
        match list with
        | [] -> s
        | head :: tail ->
            let ret = Set.union s (Map.find head rd)
            union_set ret tail rd
     
     let mutable opt = false
     let mutable retlist = []
     for node in NodeList do
        let instr = getInstr node cfg
        let suc = getSuccs node cfg 
        let la_out_node = union_set Set.empty<Register> suc laSet
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

// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  // mem 2 reg
  let m2r, instrs = Mem2Reg.run instrs
  
  // ConstantFolding
  let cf, instrs = ConstantFolding.run instrs
  
  // ConstantPropagation
  let cp, instrs = ConstantPropagation.run instrs
  
  // DeadCodeElimination 
  let dce, instrs = DeadCodeElimination.run instrs
  
  if
      m2r ||
      cf ||
      cp ||
      dce ||
      false
      then
          optimizeLoop instrs else instrs
          // instrs else instrs // 한 번만 돌게..
    
// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  (fname, args, optimizeLoop instrs)
