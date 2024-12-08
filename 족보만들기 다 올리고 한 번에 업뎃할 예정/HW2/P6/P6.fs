module P6

/// From list 'l', find the element that appears most frequently in the list,
/// and return how many times it appears. If the input list is empty, return 0.
let countMostFrequent (l: List<'a>) : int =
    
    let mutable freq = 0
    
    let rec count (l2: List<'a>) (i: 'a) : int =
        match l2 with
        | [] -> 0
        | head :: tail ->
            if head = i then 1 + (count tail i) else count tail i
    
    let rec helper (l3 : List<'a>) : unit =
      match l3 with
      | [] -> ()
      | head :: tail ->
          let k = count l head
          if k > freq then freq <- k else ()
          helper tail
          
    helper l
    freq