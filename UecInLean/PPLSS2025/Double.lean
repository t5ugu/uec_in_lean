-- Extrinsic:
--   sort: List T -> List T
--   sort_correct: (l: List T) -> Sorted (sort l)

-- Intrinsic:
--   sort: List T -> SortedList T

def double : Nat -> Nat
  | 0     => 0
  | n + 1 => .succ (.succ (double n))

