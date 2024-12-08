module P5

/// For int list 'l' that contains decimal digits (0~9), return the integer that
/// is represented by this list. For example, "digitsToInt [1; 3; 2]" must
/// return 132 as a result. When the input list is empty, just return 0.
let rec digitsToInt (l: int list) : int =
  let rec helper (acc: int) (l2 : int list) : int =
      match l2 with
      | [] -> acc
      | head :: tail -> helper(acc * 10 + head) tail
  helper 0 l
