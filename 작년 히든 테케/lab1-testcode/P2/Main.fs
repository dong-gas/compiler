open P2

let test inp ans =
  try if eval inp = ans then "O" else "X" with _ -> "E"

let testException inp =
  try (ignore (eval inp); "X") with
  | DivByZero -> "O"
  | _ -> "E"

let e1 = Sub (Num 5, Sub (Num 2, Num 1)) // 5 - (2 - 1)
let e2 = Add (Num 3, Div (Num 0, Num 2)) // 3 + 0 / 2
let e3 = Mul (Add (Num 2, Num 3), Sub (Num 4, Num 2)) // (2 + 3) * (4 - 2)
let e4 = Mul (Num 5, Div (Num 1, Num 2)) // 5 * (1 / 2)
let e5 = Div (Num 5, Sub (Num 3, Num 3)) // 5 / (3 - 3)
let r1 = test e1 4
let r2 = test e2 3
let r3 = test e3 10
let r4 = test e4 0
let r5 = testException e5
let _ = printfn "%s%s%s%s%s" r1 r2 r3 r4 r5
