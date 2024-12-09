module DFA

open CFG.CFG
open IR
open CFG


// You can represent a 'reaching definition' element with an instruction.
// 각 CFG 노드에서 도달 가능한 Instr 집합..
type RDSet = Set<Instr>

// Register Set (String)
type LASet = Set<Register> 

// CFG:
// InstrMap ToEdgeMap FromEdgeMap
// getAllNodes cfg : int list로 모든 노드번호 준다.
// make ins

module RDAnalysis =
  // Write your logic to compute reaching definition set for each CFG node.
  // 각 노드마다 RDSet 저장한 Map 반환
  let run (cfg: CFG) : Map<int, RDSet> =

    let NodeList = getAllNodes cfg
    let rec out_init (list: int list) (map: Map<int, RDSet>) : Map<int, RDSet> =
        match list with
        | [] -> map
        | head :: tail ->
            let updatedMap = map.Add(head, Set.empty<Instr>)
            out_init tail updatedMap
    
    //여기까지 RD_out초기화
    
    // 겹치는 거 삭제해주기
    let del_instr (rd_set: RDSet) (reg: Register) : RDSet =
        Set.filter (fun instr ->
            match instr with
            | Set (r, _) ->
                printfn "Checking Set: %A against %A" r reg
                r <> reg
            //| LocalAlloc (r, _) -> r <> reg
            | UnOp (r, _, _) ->
                printfn "Checking UnOp: %A against %A" r reg
                r <> reg
            | BinOp (r, _, _, _) ->
                printfn "Checking BinOp: %A against %A" r reg
                r <> reg
            | Load (r, _) ->
                printfn "Checking Load: %A against %A" r reg
                r <> reg
            // | Store (_, r) -> r <> reg
            | _ -> true
        ) rd_set 
            
    let f (rd_in: RDSet) (instr: Instr) : RDSet =
        // 만약 instr이 대입이 아니면 걍 바로 rd_in 리턴하면 됨
        // instr :  %t = ...
        // f(rd_in, instr) = (rd_in - define %t) + instr
        match instr with
        | Set (r, o)  ->
            //rd_in에서 r이 정의된 게 있으면 삭제하고
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        // | LocalAlloc (r, n) ->
        //     let rd_out = del_instr rd_in r
        //     rd_out.Add instr
        | UnOp (r, _, _) ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        | BinOp(r, _, _, _) ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        | Load (r, _) ->
            let rd_out = del_instr rd_in r
            rd_out.Add instr
        // | Store (_, r) ->
        //     let rd_out = del_instr rd_in r
        //     rd_out.Add instr
        | _ -> rd_in
    
    let rec union_set (s: RDSet) (list: int list) (rd: Map<int, RDSet>) : RDSet =
        match list with
        | [] -> s
        | head :: tail ->
            let ret = Set.union s (Map.find head rd)
            union_set ret tail rd
            

    let rec iterate (currentRD: Map<int, RDSet>) : Map<int, RDSet> =
        // printf "hello\n"
        let mutable updatedRD = currentRD
        for node in NodeList do
            let instr = getInstr node cfg
            let pre = getPreds node cfg // int list
            let rd_in_node = union_set Set.empty<Instr> pre updatedRD
            let rd_out_node = f rd_in_node instr
            updatedRD <- updatedRD.Add(node, rd_out_node)
        let ret = updatedRD
        if ret = currentRD then ret else iterate ret
            
            
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
                
    // let initialMap = in_init NodeList Map.empty<int, LASet>    
    // printfn "Initial Map: %A" initialMap
    
    //여기까지 LA_in초기화
    
        
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
            
            
    let f (la_out: LASet) (instr: Instr) : LASet =
        // la_out - def(instr) + use(instr)
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

        if changed then
            iterate updatedLA
        else
            updatedLA
    iterate (in_init NodeList Map.empty<int, LASet>)