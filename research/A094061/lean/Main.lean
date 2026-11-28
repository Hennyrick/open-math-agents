import A094061Dev.Bridge
import A094061Dev.Sec4

/-!
Glue: the A094061 target from KEY for the king polynomial.
-/

namespace A094061

open MvPowerSeries

/-- The king polynomial as a two-variable power series over ℚ. -/
noncomputable def Kps : PS :=
  ((MvPolynomial.map (Int.castRingHom ℚ) Kp : MvPolynomial (Fin 2) ℚ) : PS)

lemma coeff_Kps_pow (n : ℕ) (d : Fin 2 →₀ ℕ) :
    coeff d (Kps ^ n) = ((MvPolynomial.coeff d (Kp ^ n) : ℤ) : ℚ) := by
  rw [Kps, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe, ← map_pow, MvPolynomial.coeff_map]
  rfl

lemma const_Kps : constantCoeff Kps = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have := coeff_Kps_pow 1 0
  rw [pow_one, pow_one] at this
  rw [this, Kp_eq]
  have h0 : ∀ q : MvPolynomial (Fin 2) ℤ, MvPolynomial.coeff 0 q = MvPolynomial.constantCoeff q :=
    fun q => by rw [MvPolynomial.constantCoeff_eq]
  rw [h0]
  simp

lemma PInt_Kps {p : ℕ} (hp : p.Prime) : PInt p Kps := fun d => by
  have := coeff_Kps_pow 1 d
  rw [pow_one, pow_one] at this
  rw [this]; exact pint_int hp _

lemma a_eq_coeff_Kps (n : ℕ) :
    ((OMA.S_oeis_a094061.a n : ℤ) : ℚ) = coeff (bideg n) (Kps ^ n) := by
  rw [coeff_Kps_pow, a_eq_coeff]; rfl

/-- KEY for the king polynomial at the prime `p`. -/
def KEY (p : ℕ) (hp0 : p ≠ 0) : Prop :=
  ∃ A B : PS, PInt p A ∧ PInt p B ∧ Lser p hp0 Kps = D 0 A + D 1 B

theorem main_of_KEY (hKEY : ∀ p (hp : p.Prime), 5 ≤ p → KEY p hp.ne_zero) :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      OMA.S_oeis_a094061.a (n * p ^ k) ≡ OMA.S_oeis_a094061.a (n * p ^ (k - 1))
        [MOD p ^ (2 * k)] := by
  intro p n k hp hp5 _ hk
  obtain ⟨A, B, hA, hB, hE⟩ := hKEY p hp hp5
  have h := sec4 hp hp5 Kps const_Kps (PInt_Kps hp) A B hA hB hE n k hk
  rw [← a_eq_coeff_Kps, ← a_eq_coeff_Kps] at h
  have h2 : ((p : ℤ) ^ (2 * k)) ∣ ((OMA.S_oeis_a094061.a (n * p ^ k) : ℤ) -
      (OMA.S_oeis_a094061.a (n * p ^ (k - 1)) : ℤ)) := by
    apply dvd_of_pint hp
    push_cast
    exact h
  rw [Nat.modEq_iff_dvd]
  have := dvd_neg.2 h2
  rw [neg_sub] at this
  push_cast
  exact this

end A094061
