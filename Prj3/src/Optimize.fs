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
    | _ -> (false, instr)

  let run instrs =
    let results = List.map foldConstant instrs
    let flags, instrs = List.unzip results
    let isOptimized = List.contains true flags
    (isOptimized, instrs)
    
    
module ConstantPropagation =
    
    let run instrs =
        let cfg = CFG.make instrs                  // Control Flow Graph 생성
        let rdMap = RDAnalysis.run cfg            // Reaching Definition 결과
        let nodes = getAllNodes cfg               // 모든 노드 가져오기
        let mutable isOptimized = false          // 최적화 여부 추적
        
        // rdMap
        // |> Map.iter (fun key instr -> 
        //     printfn "Key: %d, Instr: %A" key instr
        // )
        
        let optimized_instrs =
            nodes
            |> List.fold (fun acc node ->
                let pre = getPreds node cfg       // 선행 노드 가져오기
                let instr = getInstr node cfg     // 현재 노드의 명령어 가져오기

                // rd_in 집합 계산 (선행 노드의 rd_out 합집합)
                let rd_in =
                    pre
                    |> List.fold (fun acc p -> 
                        let rd_out = Map.tryFind p rdMap |> Option.defaultValue Set.empty
                        Set.union acc rd_out
                    ) Set.empty

                // rd_in에서 특정 변수에 대한 상수 정의 확인
                let isConstant var =
                    let defs =
                        rd_in
                        |> Set.filter (fun rd ->
                            match rd with
                            | Set(r, Imm(v)) when r = var -> true
                            | _ -> false
                        )
                    //printfn "Defs for %s: %A" var defs // 변수에 대한 정의 출력
                    match Set.toList defs with
                    | [Set(_, Imm(value))] -> Some value
                    | _ -> None

                // 명령어 수정
                let new_instr =
                    match instr with
                    | BinOp(r, op, Reg(x), y) ->
                        match isConstant x with
                        | Some(value) -> BinOp(r, op, Imm(value), y)
                        | None -> instr
                    | BinOp(r, op, y, Reg(x)) ->
                        match isConstant x with
                        | Some(value) -> BinOp(r, op, y, Imm(value))
                        | None -> instr
                    | Set(r, Reg(x)) ->
                        match isConstant x with
                        | Some(value) -> Set(r, Imm(value))
                        | None -> instr
                    | _ -> instr

                if new_instr <> instr then
                    //printfn "Optimized: %A -> %A" instr new_instr
                    isOptimized <- true

                new_instr :: acc
            ) []

        (isOptimized, List.rev optimized_instrs)
  // let run instrs =
  //   let optimized_instrs = List.empty<Instr>
  //   let cfg = CFG.make instrs
  //   let rdMap = RDAnalysis.run cfg
  //   let nodes = getAllNodes cfg
  //   let mutable isOptimized = false
  //   
  //   for node in nodes do
  //     let pre = getPreds node cfg // int list..
  //     let instr = getInstr node cfg
  //     // rdMap[pre]를 다 합친 set을 만들고 싶어
  //     // 그리고 그 크기가 1이면서 안에 든 Instr값이 상수인지 확인하고 싶어
  //     // 만약 그렇다면 현재 node의 instr에 그 값이 있는지 확인하고 있다면 수정해서 
  //     // 없다면 그냥 instr 그대로 optimized_instrs에 넣고싶어
  //     isOptimized <- true
  //   (isOptimized, instrs)
    
module Mem2Reg =
  // 메모리 접근을 레지스터로 바꾸기...
  // alloc 찾아..
  let run instrs =
    // 1. localalloc 찾아. ex) %t1 = alloc 4
    // 2. 그게 최적화 할 수 있는 놈인지 체크
    // 3. 있으면 localalloc 삭제하고
    // 4. store o, %t1 을 %t1 = o로 (set) 변경
    // 5. %t2 = load %t1을 set
    let cfg = CFG.make instrs
    // (false, instrs)
    let can index instr instrs =
        match instr with
        | LocalAlloc (reg, _) ->
            // LocalAlloc일 경우, 주변 2개씩이 모두 Label이어야 true
            let isLabel i =
                if i < 0 || i >= List.length instrs then false
                else 
                    match List.tryItem i instrs with
                    | Some (Label _) -> true
                    | _ -> false
            if (isLabel (index - 2) && isLabel (index - 1) && isLabel (index + 1) && isLabel (index + 2))
                then Some reg else None
        | _ -> None  // LocalAlloc이 아닌 경우에는 None..
    
    let mutable R = None
    let mutable x = -1
    List.iteri (fun index instr ->
        // value가 localalloc이고, index-1, index-2, index+1, index+2가 모두 label이면.. 가능
        // 단순 Int, bool이면 앞뒤로 label 2개씩 넣어둠.
        let ret = can index instr instrs
        if  ret <> None then
            x <- index
            R <- ret
    ) instrs
    
    if x = -1 then (false, instrs)
    else
        // instrs에서 index번째 register가 뭔지 찾아.
        // 그리고 그 index번째 instr 삭제하고
        // 그 register가 store, load되는 instr들을 set으로 변경해서 리턴
        
        // printf "%d\n" x
        // printf "%A\n" R
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
                        //printfn "remove"
                    | _ -> true
                )
            
        let retlist = instrs
        let retlist = replace_load_to_set retlist
        let retlist = replace_store_to_set retlist
        let retlist = remove_localAlloc retlist
        (true, retlist)


// You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =
  //printfn "haa..."
  let cfg = CFG.make instrs
  let m2r, instrs = Mem2Reg.run instrs
  // let cp, instrs = ConstantPropagation.run instrs
  let cf, instrs = ConstantFolding.run instrs
  //if cp || cf then optimizeLoop instrs else instrs
  if m2r || cf then optimizeLoop instrs else instrs
  // if cf then optimizeLoop instrs else instrs

// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
  let (fname, args, instrs) = ir
  (fname, args, optimizeLoop instrs)
