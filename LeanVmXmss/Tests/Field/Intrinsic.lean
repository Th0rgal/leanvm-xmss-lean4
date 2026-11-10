set_option linter.unusedVariables false

def clmul64 (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if h : i < 64 then
      let sh := i.toUInt64
      go (i + 1) (if ((b >>> sh) &&& 1) == 1 then acc ^^^ (a <<< sh) else acc)
    else
      acc
  termination_by 64 - i
  decreasing_by exact Nat.sub_lt_sub_left h (Nat.lt_succ_self i)
  go 0 0

def clmul64Hi (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if h : i < 64 then
      let sh := i.toUInt64
      go (i + 1) (if ((b >>> sh) &&& 1) == 1 then acc ^^^ (a >>> (64 - sh)) else acc)
    else
      acc
  termination_by 64 - i
  decreasing_by exact Nat.sub_lt_sub_left h (Nat.lt_succ_self i)
  go 1 0
