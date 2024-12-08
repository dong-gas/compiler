(* Return the summation of integer from 0 to n. Assume that n >= 0. *)
let rec sum_to_n n =
  (* TODO *)
  if n = 0 then 0
  else n + sum_to_n (n - 1)

