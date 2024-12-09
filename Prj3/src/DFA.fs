module DFA

open CFG.CFG
open IR
open CFG

type RDSet = Set<Instr>
type LASet = Set<Register> 

module RDAnalysis =
  let run (cfg: CFG) : Map<int, RDSet> =
    let NodeList = getAllNodes cfg
    
    let rec out_init (list: int list) (map: Map<int, RDSet>) : Map<int, RDSet> =
        match list with
        | [] -> map
        | head :: tail ->
            let updatedMap = map.Add(head, Set.empty<Instr>)
            out_init tail updatedMap
    
    let del_instr (rd_set: RDSet) (reg: Register) : RDSet =
        Set.filter (fun instr ->
            match instr with
            | Set (r, _) -> r <> reg
            | UnOp (r, _, _) -> r <> reg
            | BinOp (r, _, _, _) -> r <> reg
            | Load (r, _) -> r <> reg
            | _ -> true
        ) rd_set 
            
    let f (rd_in: RDSet) (instr: Instr) : RDSet =
        // f(rd_in, instr) = (rd_in - define %t) + instr
        match instr with
        | Set (r, o)  ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        | UnOp (r, _, _) ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        | BinOp(r, _, _, _) ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        | Load (r, _) ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        | _ -> rd_in
    
    let rec union_set (s: RDSet) (list: int list) (rd: Map<int, RDSet>) : RDSet =
        match list with
        | [] -> s
        | head :: tail ->
            let ret = Set.union s (Map.find head rd)
            union_set ret tail rd
  
    let rec iterate (currentRD: Map<int, RDSet>) : Map<int, RDSet> =
        let mutable updatedRD = currentRD
        let mutable changed = false
        for node in NodeList do
            let instr = getInstr node cfg
            let pre = getPreds node cfg // int list
            let rd_in_node = union_set Set.empty<Instr> pre updatedRD
            let rd_out_node = f rd_in_node instr
            
            if not (Map.containsKey node updatedRD && updatedRD[node] = rd_out_node) then
                changed <- true
                updatedRD <- updatedRD.Add(node, rd_out_node)
        
        if changed then iterate updatedRD
        else updatedRD

    iterate (out_init NodeList Map.empty<int, RDSet>)
    
    
module LAAnalysis =
  let run (cfg: CFG) : Map<int, LASet> =

    let NodeList = List.rev (getAllNodes cfg)
    
    let rec in_init (list: int list) (map: Map<int, LASet>) : Map<int, LASet> =
        match list with
        | [] -> map
        | head :: tail ->
            let updatedMap = map.Add(head, Set.empty<Register>)
            in_init tail updatedMap
            
    let Def (instr: Instr) : LASet =
        let ret = Set.empty<Register>
        match instr with
        | Set(r, _) -> Set.add r ret
        | LocalAlloc(r, _) -> Set.add r ret
        | UnOp(r, _, _) -> Set.add r ret
        | BinOp(r, _, _, _) -> Set.add r ret            
        | Load(r, _) -> Set.add r ret
        | _ -> ret
        
    let Use (instr: Instr) : LASet =
        let ret = Set.empty<Register>
        let addIfReg o set =
            match o with
            | Reg r -> Set.add r set
            | _ -> set
        match instr with
        | Set(_, o) -> addIfReg o ret
        | UnOp(_, _, o) -> addIfReg o ret
        | BinOp(_, _, o1, o2) ->
            let tmp = addIfReg o1 ret
            addIfReg o2 tmp
        | Load (_, r) -> Set.add r ret
        | Store(o, r) ->
            let tmp = addIfReg o ret
            Set.add r tmp
        | GotoIf(o, _) -> addIfReg o ret            
        | GotoIfNot(o, _) -> addIfReg o ret
        | Ret(o) -> addIfReg o ret
        | _ -> ret
            
    let f (la_out: LASet) (instr: Instr) : LASet = // la_out - def(instr) + use(instr)
        let ret = la_out
        let defset = Def instr
        let useset = Use instr
        let ret = Set.difference ret defset
        let ret = Set.union ret useset  
        ret
    
    let rec union_set (s: LASet) (list: int list) (rd: Map<int, LASet>) : LASet =
        match list with
        | [] -> s
        | head :: tail ->
            let ret = 
                if Map.containsKey head rd then
                    Set.union s (Map.find head rd)
                else
                    s
            union_set ret tail rd

    let rec iterate (currentLA: Map<int, LASet>) : Map<int, LASet> =
        let mutable updatedLA = currentLA
        let mutable changed = false

        for node in NodeList do
            let instr = getInstr node cfg
            let suc = getSuccs node cfg
            let la_out_node = union_set Set.empty<Register> suc currentLA
            let la_in_node = f la_out_node instr

            if not (Map.containsKey node updatedLA && updatedLA[node] = la_in_node) then
                changed <- true
                updatedLA <- updatedLA.Add(node, la_in_node)

        if changed then iterate updatedLA
        else updatedLA    

    iterate (in_init NodeList Map.empty<int, LASet>)