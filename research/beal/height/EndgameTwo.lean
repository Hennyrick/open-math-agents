import Endgame
import Height24
import Mathlib.NumberTheory.FLT.Basic
import FormalConjectures.Wikipedia.BealConjecture

namespace BealHeight

/-- The checked height certificate suffices at K = 2. Mathlib's
`fermatLastTheoremThree` has the type of the second argument. -/
theorem beal_of_estimate_two (estimate : UniformEstimate 2) (cubes : FermatLastTheoremFor 3) :
    BealConjecture.bealConjecture :=
  beal_of_estimate_and_certificate estimate TwoTo24.certified cubes

end BealHeight

#print axioms BealHeight.beal_of_estimate_two
