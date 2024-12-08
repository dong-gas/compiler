open P1

let test inp ans =
  try if reverse inp = ans then "O" else "X" with _ -> "E"

let r1 = test [1; 3; 5] [5; 3; 1]
let r2 = test [1; 2; 1; 3] [3; 1; 2; 1]
let r3 = test [0] [0]
let r4 = test [] []
let r5 = test [1; 2; 3; 4; 5] [5; 4; 3; 2; 1]
let _ = printfn "%s%s%s%s%s" r1 r2 r3 r4 r5
