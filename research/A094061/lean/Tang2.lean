import A094061Dev.Tang

/-!
The tangential Steinberg lemma, part 1: setup identities for `f = κ z u`.
-/

namespace A094061

open PowerSeries

section setup
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ : KK) (u : PK)

/-- `v = z u`. -/
noncomputable def vv : PK := X * u
/-- `f = κ z u`. -/
noncomputable def ff : PK := C κ * vv u
/-- `w = σ(κ) v^p`. -/
noncomputable def ww : PK := C (sig p h3 κ) * vv u ^ p
/-- `ℓ = 1 + u'/u` (log-derivative of `v`). -/
noncomputable def ell : PK := 1 + ld1 u

lemma const_vv : constantCoeff (vv u) = 0 := by simp [vv]
lemma const_ff : constantCoeff (ff κ u) = 0 := by simp [ff, const_vv]
lemma const_ww (hp0 : p ≠ 0) : constantCoeff (ww h3 κ u) = 0 := by
  simp [ww, const_vv, zero_pow hp0]

variable (hu1 : constantCoeff u = 1)
include hu1

lemma E1_vv : E1 (vv u) = vv u * ell u := by
  have hu0 : constantCoeff u ≠ 0 := by rw [hu1]; exact one_ne_zero
  rw [vv, E1_mul, E1_X, ell, ld1]
  rw [show X * u * (1 + E1 u * u⁻¹) = X * u + X * E1 u * (u⁻¹ * u) by ring,
    PowerSeries.inv_mul_cancel _ hu0]; ring

lemma E1_ff : E1 (ff κ u) = ff κ u * ell u := by
  rw [ff, E1_mul, E1_C, E1_vv u hu1]; ring

lemma E1_ww : E1 (ww h3 κ u) = ww h3 κ u * ((p : PK) * ell u) := by
  rw [ww, E1_mul, E1_C, E1_pow, E1_vv u hu1]
  rcases p with _ | p
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]; ring

end setup

section facts
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ : KK) (u : PK) (hu1 : constantCoeff u = 1)
include hp hu1

/-- `θ' = φ(u)/u^p`. -/
noncomputable def thq : PK := phi1 p hp.ne_zero h3 u * (u ^ p)⁻¹

omit hu1 in
lemma const_thq (hu1 : constantCoeff u = 1) : constantCoeff (thq hp h3 u) = 1 := by
  simp [thq, const_phi1, hu1]

lemma phi_ff : phi1 p hp.ne_zero h3 (ff κ u) = ww h3 κ u * ex1 (lg (thq hp h3 u)) := by
  rw [ex1_lg (const_thq hp h3 u hu1)]
  have hu0 : constantCoeff (u ^ p) ≠ 0 := by rw [map_pow, hu1, one_pow]; exact one_ne_zero
  rw [ff, vv, ww, vv, thq, map_mul, map_mul, phi1_C hp h3, phi1_X hp h3, mul_pow,
    show C (sig p h3 κ) * (X ^ p * u ^ p) * (phi1 p hp.ne_zero h3 u * (u ^ p)⁻¹)
      = C (sig p h3 κ) * X ^ p * phi1 p hp.ne_zero h3 u * (u ^ p * (u ^ p)⁻¹) by ring,
    PowerSeries.mul_inv_cancel _ hu0, mul_one]
  ring

lemma lg_thq : lg (thq hp h3 u) = -((p : KK) • UU hp h3 u) := by
  have hu0 : constantCoeff u ≠ 0 := by rw [hu1]; exact one_ne_zero
  have hpu : constantCoeff (u ^ p) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu0
  have hφ : constantCoeff (phi1 p hp.ne_zero h3 u) ≠ 0 := by
    rw [const_phi1, hu1, map_one]; exact one_ne_zero
  rw [thq, lg_mul hφ (by rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hpu), lg_inv hpu,
    lg_phi1 p hp.ne_zero h3 hu0, lg_pow hu0, UU, smul_sub, smul_smul, mul_inv_cancel₀ (pKK_ne hp),
    one_smul]
  ring

omit hu1 in
lemma E1_UU : E1 (UU hp h3 u) = ld1 u - phi1 p hp.ne_zero h3 (ld1 u) := by
  rw [UU, E1_sub, E1_smul, E1_phi1, E1_lg, smul_smul, inv_mul_cancel₀ (pKK_ne hp), one_smul]

omit hu1 in
lemma phi_ell : phi1 p hp.ne_zero h3 (ell u) = ell u - E1 (UU hp h3 u) := by
  rw [E1_UU, ell, map_add, map_one]; ring

lemma G_ff : (thk 2 Li2).subst (ff κ u) * (1 - ff κ u) = ff κ u := by
  have hs : HasSubst (ff κ u) := HasSubst.of_constantCoeff_zero' (const_ff κ u)
  have := congrArg (PowerSeries.subst (ff κ u)) G_mul
  have e1 : (1 : PK).subst (ff κ u) = 1 := by
    rw [show (1 : PK) = C 1 from (map_one C).symm, subst_C]; exact map_one _
  rw [subst_mul hs, subst_sub hs, subst_X hs, e1] at this
  exact this

lemma ld1_one_sub_ff : ld1 (1 - ff κ u) = -(ell u * (thk 2 Li2).subst (ff κ u)) := by
  have h1 : constantCoeff (1 - ff κ u) ≠ 0 := by simp [const_ff]
  apply cancel1 h1
  rw [ld1, mul_assoc, PowerSeries.inv_mul_cancel _ h1, mul_one, E1_sub, E1_one, zero_sub,
    E1_ff κ u hu1, neg_mul, mul_assoc, G_ff hp κ u hu1]
  ring

lemma lg_one_sub_ff : lg (1 - ff κ u) = -(thk 1 Li2).subst (ff κ u) := by
  apply eq_of_E1_eq
  · rw [E1_lg, ld1_one_sub_ff hp κ u hu1, E1_neg, E1_subst' _ (const_ff κ u) (E1_ff κ u hu1),
      ← thk_succ]
  · rw [const_lg, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_subst_range _ (const_ff κ u)]
    simp [thk, Li2]

lemma UU_one_sub_ff : UU hp h3 (1 - ff κ u) = -(thk 1 Li2).subst (ff κ u)
    + (p : KK)⁻¹ • (thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))) := by
  rw [UU, lg_one_sub_ff hp κ u hu1, map_neg, phi1_subst hp h3 (SigFix_thk_Li2 h3 1) (const_ff κ u),
    phi_ff hp h3 κ u hu1, smul_neg, sub_neg_eq_add]

end facts

end A094061
