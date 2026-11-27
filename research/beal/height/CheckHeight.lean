import Bounded

/-- Run the exact finite search at a height supplied in decimal. The corresponding
Lean theorem for a positive result is obtained with BealHeight.certifies_iff. -/
def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln "Usage: CheckHeight HEIGHT"; return 2
  let some bound := arg.toNat? | IO.eprintln "HEIGHT must be a nonnegative integer"; return 2
  if BealHeight.certifies bound then
    IO.println s!"All solutions with C^z ≤ {bound} have gcd(A, B, C) > 1."
    return 0
  else
    IO.println s!"A primitive solution exists with C^z ≤ {bound}."
    return 1
