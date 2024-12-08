module DFA

open CFG.CFG
open IR
open CFG


// You can represent a 'reaching definition' element with an instruction.
// 각 CFG 노드에서 도달 가능한 Instr 집합..
type RDSet = Set<Instr>

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
        printf "hello\n"
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