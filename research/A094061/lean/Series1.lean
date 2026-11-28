import A094061Dev.KField

/-!
One-variable power series over `ℚ(ω)`: Euler derivative, Frobenius `φ = expand ∘ σ`,
logarithm via log-derivative.
-/

namespace A094061

open PowerSeries

abbrev PK := PowerSeries KK

/-- Euler derivative `z d/dz`. -/
noncomputable def E1 (f : PK) : PK := X * d⁄dX KK f

lemma coeff_E1 (f : PK) (n : ℕ) : coeff n (E1 f) = (n : KK) * coeff n f := by
  rcases n with _ | n
  · simp [E1]
  · rw [E1, coeff_succ_X_mul, coeff_derivative]; push_cast; ring

lemma E1_mul (f g : PK) : E1 (f * g) = f * E1 g + g * E1 f := by
  simp only [E1, Derivation.leibniz, smul_eq_mul]; ring

lemma E1_add (f g : PK) : E1 (f + g) = E1 f + E1 g := by simp only [E1, map_add]; ring

lemma E1_sub (f g : PK) : E1 (f - g) = E1 f - E1 g := by simp only [E1, map_sub]; ring

lemma E1_neg (f : PK) : E1 (-f) = -E1 f := by simp only [E1, map_neg]; ring

lemma E1_smul (c : KK) (f : PK) : E1 (c • f) = c • E1 f := by
  simp only [E1]; rw [(d⁄dX KK).map_smul, mul_smul_comm]

lemma E1_C (c : KK) : E1 (C c) = 0 := by simp [E1]

lemma E1_one : E1 (1 : PK) = 0 := by simpa using E1_C 1

lemma E1_X : E1 (X : PK) = X := by simp [E1]

lemma E1_pow (f : PK) (n : ℕ) : E1 (f ^ n) = (n : PK) * f ^ (n - 1) * E1 f := by
  simp only [E1, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]; ring

lemma const_E1 (f : PK) : constantCoeff (E1 f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_E1]; simp

lemma eq_of_E1_eq {f g : PK} (h : E1 f = E1 g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  rcases n with _ | n
  · simpa [coeff_zero_eq_constantCoeff_apply] using hc
  · have := congrArg (coeff (n + 1)) h
    rw [coeff_E1, coeff_E1] at this
    exact mul_left_cancel₀ (by exact_mod_cast n.succ_ne_zero) this

lemma E1_inv {f : PK} (hf : constantCoeff f ≠ 0) : E1 f⁻¹ = -(f⁻¹ * f⁻¹) * E1 f := by
  have h := congrArg E1 (PowerSeries.mul_inv_cancel f hf)
  rw [E1_mul, E1_one] at h
  have hinv : f⁻¹ * f = 1 := PowerSeries.inv_mul_cancel f hf
  calc E1 f⁻¹ = (f⁻¹ * f) * E1 f⁻¹ := by rw [hinv, one_mul]
    _ = f⁻¹ * (f * E1 f⁻¹ + f⁻¹ * E1 f) - (f⁻¹ * f⁻¹) * E1 f := by ring
    _ = -(f⁻¹ * f⁻¹) * E1 f := by rw [h]; ring

lemma cancel1 {a b h : PK} (hh : constantCoeff h ≠ 0) (e : a * h = b * h) : a = b := by
  have := congrArg (· * h⁻¹) e
  simp only [mul_assoc, PowerSeries.mul_inv_cancel h hh, mul_one] at this
  exact this

/-- Log-derivative. -/
noncomputable def ld1 (f : PK) : PK := E1 f * f⁻¹

lemma ld1_mul {f g : PK} (hf : constantCoeff f ≠ 0) (hg : constantCoeff g ≠ 0) :
    ld1 (f * g) = ld1 f + ld1 g := by
  have hfg : constantCoeff (f * g) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hf hg
  apply cancel1 hfg
  simp only [ld1, E1_mul]
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hfg, mul_one]
  have e2 : (E1 f * f⁻¹ + E1 g * g⁻¹) * (f * g) = E1 f * g * (f⁻¹ * f) + E1 g * f * (g⁻¹ * g) := by
    ring
  rw [e2, PowerSeries.inv_mul_cancel _ hf, PowerSeries.inv_mul_cancel _ hg]; ring

lemma ld1_inv {f : PK} (hf : constantCoeff f ≠ 0) : ld1 f⁻¹ = -ld1 f := by
  have h1 : constantCoeff f⁻¹ ≠ 0 := by rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hf
  have := ld1_mul hf h1
  rw [PowerSeries.mul_inv_cancel f hf] at this
  have h0 : ld1 (1 : PK) = 0 := by simp [ld1, E1_one]
  rw [h0] at this; linear_combination (-1 : PK) * this

lemma ld1_pow {f : PK} (hf : constantCoeff f ≠ 0) (n : ℕ) : ld1 (f ^ n) = (n : KK) • ld1 f := by
  induction n with
  | zero => simp [ld1, E1_one]
  | succ n ih =>
    have hfn : constantCoeff (f ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hf
    rw [pow_succ, ld1_mul hfn hf, ih]; push_cast; rw [add_smul, one_smul]

lemma const_ld1 (f : PK) : constantCoeff (ld1 f) = 0 := by simp [ld1, const_E1]

/-- Logarithm normalised to constant term zero. -/
noncomputable def lg (f : PK) : PK := mk fun n => if n = 0 then 0 else coeff n (ld1 f) / n

lemma const_lg (f : PK) : constantCoeff (lg f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, lg, coeff_mk]; simp

lemma E1_lg (f : PK) : E1 (lg f) = ld1 f := by
  ext n
  rw [coeff_E1, lg, coeff_mk]
  rcases n with _ | n
  · simp [coeff_zero_eq_constantCoeff_apply, const_ld1]
  · simp only [Nat.succ_ne_zero, if_false]
    have : ((n + 1 : ℕ) : KK) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp

lemma lg_mul {f g : PK} (hf : constantCoeff f ≠ 0) (hg : constantCoeff g ≠ 0) :
    lg (f * g) = lg f + lg g := by
  apply eq_of_E1_eq
  · rw [E1_add, E1_lg, E1_lg, E1_lg, ld1_mul hf hg]
  · simp [const_lg]

lemma lg_inv {f : PK} (hf : constantCoeff f ≠ 0) : lg f⁻¹ = -lg f := by
  apply eq_of_E1_eq
  · rw [E1_neg, E1_lg, E1_lg, ld1_inv hf]
  · simp [const_lg]

lemma lg_pow {f : PK} (hf : constantCoeff f ≠ 0) (n : ℕ) : lg (f ^ n) = (n : KK) • lg f := by
  apply eq_of_E1_eq
  · rw [E1_smul, E1_lg, E1_lg, ld1_pow hf]
  · simp [const_lg]

/-! Frobenius `φ`. -/

section frob
variable (p : ℕ) (hp0 : p ≠ 0) (h3 : ¬ 3 ∣ p)

/-- `φ(h)(z) = h^σ(z^p)`. -/
noncomputable def phi1 : PK →+* PK :=
  (PowerSeries.expand p hp0 : PK →ₐ[KK] PK).toRingHom.comp (PowerSeries.map (sig p h3).toRingHom)

lemma coeff_phi1 (f : PK) (n : ℕ) :
    coeff n (phi1 p hp0 h3 f) = if p ∣ n then sig p h3 (coeff (n / p) f) else 0 := by
  simp [phi1, coeff_expand, coeff_map]

lemma coeff_phi1_mul (f : PK) (m : ℕ) : coeff (p * m) (phi1 p hp0 h3 f) = sig p h3 (coeff m f) := by
  rw [coeff_phi1, if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp0)]

lemma const_phi1 (f : PK) : constantCoeff (phi1 p hp0 h3 f) = sig p h3 (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    show (0 : ℕ) = p * 0 by ring, coeff_phi1_mul]
  simp

lemma E1_phi1 (f : PK) : E1 (phi1 p hp0 h3 f) = (p : KK) • phi1 p hp0 h3 (E1 f) := by
  ext n
  rw [coeff_E1, coeff_smul, coeff_phi1, coeff_phi1]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp0), coeff_E1, map_mul, map_natCast]
    push_cast; ring
  · simp

lemma phi1_inv {f : PK} (hf : constantCoeff f ≠ 0) :
    phi1 p hp0 h3 f⁻¹ = (phi1 p hp0 h3 f)⁻¹ := by
  have h1 : constantCoeff (phi1 p hp0 h3 f) ≠ 0 := by
    rw [const_phi1]; exact (map_ne_zero _).2 hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h1, ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]

lemma lg_phi1 {f : PK} (hf : constantCoeff f ≠ 0) : lg (phi1 p hp0 h3 f) = phi1 p hp0 h3 (lg f) := by
  have h1 : constantCoeff (phi1 p hp0 h3 f) ≠ 0 := by
    rw [const_phi1]; exact (map_ne_zero _).2 hf
  apply eq_of_E1_eq
  · rw [E1_lg, E1_phi1, E1_lg, ld1, ld1, map_mul, E1_phi1, phi1_inv p hp0 h3 hf, smul_mul_assoc]
  · rw [const_lg, const_phi1, const_lg, map_zero]

end frob

/-! Substitution coefficients as finite sums. -/

lemma coeff_pow_zero_of_lt {g : PK} (hg : constantCoeff g = 0) {n d : ℕ} (h : n < d) :
    coeff n (g ^ d) = 0 := by
  obtain ⟨q, hq⟩ : X ^ d ∣ g ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.2 hg) d
  rw [hq, coeff_X_pow_mul', if_neg (by omega)]

/-- Coefficients of a substitution into a series without constant term. -/
lemma coeff_subst_range (A : PK) {g : PK} (hg : constantCoeff g = 0) (n : ℕ) :
    coeff n (A.subst g) = ∑ d ∈ Finset.range (n + 1), coeff d A * coeff n (g ^ d) := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    rw [coeff_pow_zero_of_lt hg (by omega), smul_zero]


end A094061
