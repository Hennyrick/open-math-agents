import HeightBound
import Bounded
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

namespace BealHeight

/-- One constant valid uniformly for every primitive solution.  The height
is the value of the right-hand power, and the radical is that of the bases. -/
def UniformEstimate (K : ℕ) : Prop :=
  ∀ {a b c x y z : ℕ}, 0 < a → 0 < b → 0 < c → 3 ≤ x → 3 ≤ y → 3 ≤ z →
    a ^ x + b ^ y = c ^ z → Nat.gcd a (Nat.gcd b c) = 1 →
    (c ^ z) ^ 22 ≤ K ^ 22 * rad (a*b*c) ^ 23

/-- This is definitionally the type of Mathlib's fermatLastTheoremThree. -/
abbrev NoPositiveCubeSum : Prop :=
  ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3

/-- The conclusion is the defining proposition of BealConjecture.bealConjecture.
When the FLT module is imported, its theorem fermatLastTheoremThree supplies
the last argument directly. -/
theorem beal_of_estimate_and_certificate {K : ℕ} (estimate : UniformEstimate K)
    (certificate : certifies (K ^ 24) = true) (cubes : NoPositiveCubeSum) :
    ∀ {a b c x y z : ℕ}, a ≠ 0 → b ≠ 0 → c ≠ 0 → 2 < x → 2 < y → 2 < z →
      a ^ x + b ^ y = c ^ z → 1 < Finset.gcd {a, b, c} id := by
  intro a b c x y z ha hb hc hx hy hz he
  have ha' := Nat.pos_of_ne_zero ha
  have hb' := Nat.pos_of_ne_zero hb
  have hc' := Nat.pos_of_ne_zero hc
  simp only [Finset.gcd_insert, Finset.gcd_singleton, id_eq, normalize_eq, gcd_eq_nat_gcd]
  change 1 < Nat.gcd a (Nat.gcd b c)
  by_cases large : 4 ≤ x ∨ 4 ≤ y ∨ 4 ≤ z
  · by_contra hxg
    have hgpos := Nat.gcd_pos_of_pos_left (Nat.gcd b c) ha'
    have hprim : Nat.gcd a (Nat.gcd b c) = 1 := by omega
    have gap := radical_gap ha' hb' hc' hx hy hz large he
    have bound := cutoff (Nat.pow_pos hc') gap (estimate ha' hb' hc' hx hy hz he hprim)
    exact hxg ((certifies_iff (K ^ 24)).mp certificate ha hb hc hx hy hz he bound.le)
  · have ex : x = 3 := by omega
    have ey : y = 3 := by omega
    have ez : z = 3 := by omega
    subst x
    subst y
    subst z
    exact False.elim (cubes a b c ha hb hc he)

end BealHeight
