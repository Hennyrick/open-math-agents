import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

namespace BealCartanProduct

private def signAtResidue (r : ℕ) : ℤ :=
  if r = 0 then 0 else if r = 1 ∨ r = 4 then 1 else -1

/-- The quadratic character modulo five, including its value zero at multiples of five. -/
def chi5 (n : ℕ) : ℤ := signAtResidue (n % 5)

theorem chi5_mul (a b : ℕ) : chi5 (a * b) = chi5 a * chi5 b := by
  have table : ∀ i j : Fin 5, signAtResidue (i.val * j.val % 5) =
      signAtResidue i.val * signAtResidue j.val := by decide
  unfold chi5
  rw [Nat.mul_mod]
  exact table ⟨a % 5, Nat.mod_lt _ (by decide)⟩ ⟨b % 5, Nat.mod_lt _ (by decide)⟩

private theorem multiplicative_induction {P : ℕ → Prop} (one : P 1)
    (mul : ∀ a b, P a → P b → P (a*b)) (B : ℕ) (hB : B ≠ 0)
    (primes : ∀ l : ℕ, l.Prime → l ∣ B → P l) : P B := by
  induction B using Nat.strong_induction_on with
  | h B ih =>
    by_cases h1 : B = 1
    · simpa [h1] using one
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd h1
    have hk0 : k ≠ 0 := by rintro rfl; simp_all
    have hlt : k < B := by
      have := Nat.mul_le_mul_right k hl.two_le
      omega
    have hlk : P k := ih k hlt hk0 fun m hm hd =>
      primes m hm (hd.trans (hk ▸ dvd_mul_left k l))
    exact hk ▸ mul l k (primes l hl ⟨k,hk⟩) hlk

/-- Multiply the local Cartan congruences with the multiplicities in B. -/
theorem square_eq_chi5_of_prime_divisors {B p : ℕ} (hB : B.Coprime 5)
    (primes : ∀ l : ℕ, l.Prime → l ∣ B →
      (l : ZMod p)^2 = (chi5 l : ZMod p)) :
    (B : ZMod p)^2 = (chi5 B : ZMod p) := by
  have h0 : B ≠ 0 := by rintro rfl; exact (by decide : ¬Nat.Coprime 0 5) hB
  apply multiplicative_induction (P := fun n => (n : ZMod p)^2 = (chi5 n : ZMod p))
      _ _ B h0 primes
  · simp [chi5, signAtResidue]
  · intro a b ha hb
    rw [Nat.cast_mul, mul_pow, chi5_mul, Int.cast_mul, ha, hb]

/-- Being congruent to either 1 or -1 also passes from prime divisors to
their product. The modulus may in particular be 5p. -/
theorem plus_or_minus_one_of_prime_divisors {B m : ℕ} (hB : B ≠ 0)
    (primes : ∀ l : ℕ, l.Prime → l ∣ B →
      (l : ZMod m) = 1 ∨ (l : ZMod m) = -1) :
    (B : ZMod m) = 1 ∨ (B : ZMod m) = -1 := by
  apply multiplicative_induction
      (P := fun n => (n : ZMod m) = 1 ∨ (n : ZMod m) = -1) _ _ B hB primes
  · exact Or.inl Nat.cast_one
  · intro a b ha hb
    rw [Nat.cast_mul]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

end BealCartanProduct
