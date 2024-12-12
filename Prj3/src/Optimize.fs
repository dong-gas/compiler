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
    | BinOp (r, DivOp, Imm x, Imm y) ->
        match y with
        | 0 -> (false, instr)
        | _ -> (true, Set (r, Imm (x / y)))
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
        let rdMap = RDAnalysis.run cfg
        let NodeList = getAllNodes cfg
        let rec union_set (s: RDSet) (list: int list) (rd: Map<int, RDSet>) : RDSet =
            match list with
            | [] -> s
            | head :: tail ->
                let ret = Set.union s (Map.find head rd)
                union_set ret tail rd
        let mutable opt = false 
        let mutable retlist = []
        for node in NodeList do
            let instr = getInstr node cfg
            let pre = getPreds node cfg
            let rd_in_node = union_set Set.empty<Instr> pre rdMap
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
                    retlist <- retlist @ [Set(r, Imm c)]
                | None -> retlist <- retlist @ [instr]
            | UnOp(r, un, o) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [UnOp(r, un, Imm c)]
                | None -> retlist <- retlist @ [instr]
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
                | None, None -> retlist <- retlist @ [instr]
            | Store(o, r) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [Store(Imm c, r)]
                | None -> retlist <- retlist @ [instr]
            | GotoIf(o, l) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [GotoIf(Imm c, l)]
                | None -> retlist <- retlist @ [instr]
            | GotoIfNot(o, l) ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [GotoIfNot(Imm c, l)]
                | None -> retlist <- retlist @ [instr]
            | Ret o ->
                match can o with
                | Some c ->
                    opt <- true
                    retlist <- retlist @ [Ret(Imm c)]
                | None -> retlist <- retlist @ [instr]
            | _ -> retlist <- retlist @ [instr]
        (opt, retlist)

    
module Mem2Reg =
  let run instrs =
    let trash = "trash"
    let can index instr instrs =
        match instr with
        | LocalAlloc (reg, _) ->
            let isLabel i =
                if i < 0 || i >= List.length instrs then false
                else 
                    match List.tryItem i instrs with
                    | Some (Label l) when l = trash -> true
                    | _ -> false
            if (isLabel (index - 1) && isLabel (index + 1)) then
                if not (List.exists (function Label l when l = reg -> true | _ -> false) instrs) then Some reg
                else None
            else None
        | _ -> None
    
    let mutable R = None
    let mutable x = -1
    List.iteri (fun index instr ->
        let ret = can index instr instrs
        if  ret <> None && x = -1 then
            x <- index
            R <- ret
    ) instrs
    
    if x = -1 then (false, instrs) else
        let replace_store_to_set (lst: Instr List) =
            lst |> List.map (fun x ->
                        match x with
                        | Store(o, reg) ->
                            if Some reg = R then Set(reg, o)
                            else x
                        | _ -> x 
                )
        let replace_load_to_set (lst: Instr list) =
            lst |> List.map (fun x ->
                        match x with
                        | Load(r1, reg) ->
                            if Some reg = R then Set(r1, Reg reg)
                            else x
                        | _ -> x
                )
        let remove_localAlloc (lst: Instr list) =
            lst |> List.filter (fun x ->
                    match x with
                    | LocalAlloc(reg, _) -> Some reg <> R
                    | _ -> true
                )
        let retlist = instrs
        let retlist = remove_localAlloc retlist
        let retlist = replace_load_to_set retlist
        let retlist = replace_store_to_set retlist
        
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

module CopyPropagation =
  let run instrs =
    let mutable opt = false
    
    (opt, instrs)
    
module CommonSubexpressionElimination =
    let run instrs =
        let cfg = CFG.make instrs
        let AESet = AEAnalysis.run cfg    
        let NodeList = getAllNodes cfg
        let rec intersection_set (s: AESet) (list: int list) (ae: Map<int, AESet>) : AESet =
            match list with
            | [] -> s
            | head :: tail ->
                let ret = Set.intersect s (Map.find head ae)
                intersection_set ret tail ae
        let mutable opt = false
        let mutable retlist = []
        let mutable U = Set.empty<Instr>
        for node in NodeList do
            let instr = getInstr node cfg
            U <- Set.add instr U
            
        for node in NodeList do
            let instr = getInstr node cfg
            let pre = getPreds node cfg 
            let ae_out_node = intersection_set U pre AESet
            match instr with
            | UnOp(r, un, o) ->
                let get_same_exp = 
                    ae_out_node 
                    |> Set.filter (fun instr ->
                        match instr with
                        | UnOp(sr, sun, so) -> sun = un && so = o
                        | _ -> false
                        )
                match Set.toList get_same_exp with
                | [UnOp(sr, _, _)] ->
                    opt <- true
                    retlist <- Set(r, Reg sr) :: retlist
                | _ ->retlist <- instr :: retlist
            | BinOp(r, bin, o1, o2) ->
                let get_same_exp = 
                    ae_out_node 
                    |> Set.filter (fun instr ->
                        match instr with
                        | BinOp(sr, sbin, so1, so2) -> sbin = bin && so1 = o1 && so2 = o2
                        | _ -> false
                        )
                match Set.toList get_same_exp with
                | [BinOp(sr, _, _, _)] ->
                    opt <- true
                    retlist <- Set(r, Reg sr) :: retlist
                | _ ->retlist <- instr :: retlist
            // | Set(o, r) -> // r = o
                // o가 우변인 걸 찾아서 그 좌변으로 대체..
                // 이건 copy prop에서 해야겠구나. 여기선 의미가 없구나...?
            | _ -> retlist <- instr :: retlist
            
        // if opt then printfn "HELLO"
        (opt, List.rev retlist)

// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  
  // Mem2Reg
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let m2r, instrs = Mem2Reg.run instrs
  
  // ConstantFolding
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let cons_fold, instrs = ConstantFolding.run instrs
  
  // ConstantPropagation
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let cons_prop, instrs = ConstantPropagation.run instrs
  
  // CopyPropagation
  // XXXXXXXXXXXXXXXXXXXXXXXXXXX
  // let copy_prop, instrs = CopyPropagation.run instrs
  
  // CommonSubexpressionElimination
  // XXXXXXXXXXXXXXXXXXXXXXXXXXX
  let cse, instrs = CommonSubexpressionElimination.run instrs
  
  // DeadCodeElimination
  // OOOOOOOOOOOOOOOOOOOOOOOOOOO
  let dce, instrs = DeadCodeElimination.run instrs
  
  if
      m2r ||
      cons_fold ||
      cons_prop || 
      // copy_prop ||
      cse ||
      dce ||
      false
      then
          optimizeLoop instrs else instrs
          // instrs else instrs // 한 번만 돌게..
    
// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  (fname, args, optimizeLoop instrs)