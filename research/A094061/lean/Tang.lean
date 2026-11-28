import A094061Dev.Series1

/-!
Tools for the tangential Steinberg lemma: congruences modulo `X^(K+1)`, the Euler chain rule,
the exponential, and the Taylor identity `A(w e^t) ≡ ∑ t^k/k! (θ^k A)(w)`.
-/

namespace A094061

open PowerSeries

/-- `f ≡ g mod X^(K+1)`. -/
def TQ (K : ℕ) (f g : PK) : Prop := X ^ (K + 1) ∣ f - g

lemma TQ.refl (K : ℕ) (f : PK) : TQ K f f := by simp [TQ]

lemma TQ.symm {K : ℕ} {f g : PK} (h : TQ K f g) : TQ K g f := by
  unfold TQ at *; rw [← neg_sub]; exact (dvd_neg).2 h

lemma TQ.trans {K : ℕ} {f g h : PK} (h1 : TQ K f g) (h2 : TQ K g h) : TQ K f h := by
  unfold TQ at *; rw [show f - h = (f - g) + (g - h) by ring]; exact dvd_add h1 h2

lemma TQ.add {K : ℕ} {f g f' g' : PK} (h1 : TQ K f g) (h2 : TQ K f' g') : TQ K (f + f') (g + g') := by
  unfold TQ at *; rw [show f + f' - (g + g') = (f - g) + (f' - g') by ring]; exact dvd_add h1 h2

lemma TQ.sub {K : ℕ} {f g f' g' : PK} (h1 : TQ K f g) (h2 : TQ K f' g') : TQ K (f - f') (g - g') := by
  unfold TQ at *; rw [show f - f' - (g - g') = (f - g) - (f' - g') by ring]; exact dvd_sub h1 h2

lemma TQ.mul {K : ℕ} {f g f' g' : PK} (h1 : TQ K f g) (h2 : TQ K f' g') : TQ K (f * f') (g * g') := by
  unfold TQ at *
  rw [show f * f' - g * g' = (f - g) * f' + g * (f' - g') by ring]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

lemma TQ.mul_left {K : ℕ} (c : PK) {f g : PK} (h : TQ K f g) : TQ K (c * f) (c * g) :=
  (TQ.refl K c).mul h

lemma TQ.sum {K : ℕ} {ι : Type*} (s : Finset ι) (f g : ι → PK) (h : ∀ i ∈ s, TQ K (f i) (g i)) :
    TQ K (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  unfold TQ at *; rw [← Finset.sum_sub_distrib]; exact Finset.dvd_sum h

lemma TQ_coeff {K : ℕ} {f g : PK} (h : TQ K f g) {n : ℕ} (hn : n ≤ K) : coeff n f = coeff n g := by
  obtain ⟨q, hq⟩ := h
  have := congrArg (coeff n) hq
  rw [map_sub, coeff_X_pow_mul', if_neg (by omega)] at this
  exact sub_eq_zero.1 this

lemma TQ_of_coeff {K : ℕ} {f g : PK} (h : ∀ n ≤ K, coeff n f = coeff n g) : TQ K f g := by
  unfold TQ; rw [X_pow_dvd_iff]
  intro m hm; rw [map_sub, h m (by omega), sub_self]

lemma TQ_zero_of_pow {K : ℕ} {g : PK} (hg : constantCoeff g = 0) {d : ℕ} (hd : K < d) :
    TQ K (g ^ d) 0 := by
  unfold TQ; rw [sub_zero]
  exact (pow_dvd_pow X hd).trans (pow_dvd_pow_of_dvd (X_dvd_iff.2 hg) d)

/-- Substitution agrees with a finite partial sum modulo `X^(K+1)`. -/
lemma TQ_subst (A : PK) {g : PK} (hg : constantCoeff g = 0) (K : ℕ) :
    TQ K (A.subst g) (∑ d ∈ Finset.range (K + 1), C (coeff d A) * g ^ d) := by
  apply TQ_of_coeff
  intro n hn
  rw [coeff_subst_range A hg, map_sum]
  simp only [coeff_C_mul]
  apply Finset.sum_subset
  · intro d hd; simp at hd ⊢; omega
  · intro d _ hd; simp at hd; rw [coeff_pow_zero_of_lt hg (by omega), mul_zero]

/-! Euler chain rule. -/

lemma E1_subst (A : PK) {g : PK} (hg : constantCoeff g = 0) :
    E1 (A.subst g) = E1 g * (d⁄dX KK A).subst g := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [E1, derivative_subst hs, E1]; ring

/-- If `E1 g = g * m` then `E1 (A ∘ g) = m * (E1 A) ∘ g`. -/
lemma E1_subst' (A : PK) {g m : PK} (hg : constantCoeff g = 0) (hm : E1 g = g * m) :
    E1 (A.subst g) = m * (E1 A).subst g := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [E1_subst A hg, hm, show E1 A = X * d⁄dX KK A from rfl, subst_mul hs, subst_X hs]; ring

/-! The exponential. -/

/-- `exp ∘ t`. -/
noncomputable def ex1 (t : PK) : PK := (PowerSeries.exp KK).subst t

lemma const_ex1 {t : PK} (ht : constantCoeff t = 0) : constantCoeff (ex1 t) = 1 := by
  rw [ex1, ← coeff_zero_eq_constantCoeff_apply, coeff_subst_range _ ht]; simp

lemma E1_ex1 {t : PK} (ht : constantCoeff t = 0) : E1 (ex1 t) = E1 t * ex1 t := by
  rw [ex1, E1_subst _ ht, derivative_exp]

/-- A unit is determined by its log-derivative and constant term. -/
lemma eq_of_ld1_eq {a b : PK} (ha : constantCoeff a ≠ 0) (hb : constantCoeff b ≠ 0)
    (h : E1 a * b = E1 b * a) (hc : constantCoeff a = constantCoeff b) : a = b := by
  have hq : E1 (a * b⁻¹) = 0 := by
    rw [E1_mul, E1_inv hb]
    have : a * (-(b⁻¹ * b⁻¹) * E1 b) + b⁻¹ * E1 a = b⁻¹ * b⁻¹ * (E1 a * b - E1 b * a) := by
      rw [show b⁻¹ * b⁻¹ * (E1 a * b - E1 b * a) = E1 a * (b⁻¹ * b) * b⁻¹ - b⁻¹ * b⁻¹ * E1 b * a
        by ring, PowerSeries.inv_mul_cancel _ hb]; ring
    rw [this, h, sub_self, mul_zero]
  have h1 : a * b⁻¹ = 1 := by
    apply eq_of_E1_eq (by rw [hq, E1_one])
    rw [map_mul, PowerSeries.constantCoeff_inv, hc, mul_inv_cancel₀ hb, map_one]
  have := congrArg (· * b) h1
  simp only [mul_assoc, PowerSeries.inv_mul_cancel _ hb, mul_one, one_mul] at this
  exact this

lemma ex1_lg {f : PK} (hf : constantCoeff f = 1) : ex1 (lg f) = f := by
  have hf0 : constantCoeff f ≠ 0 := by rw [hf]; exact one_ne_zero
  apply eq_of_ld1_eq (by rw [const_ex1 (const_lg f)]; exact one_ne_zero) hf0
  · rw [E1_ex1 (const_lg f), E1_lg, ld1]
    rw [show E1 f * f⁻¹ * ex1 (lg f) * f = E1 f * ex1 (lg f) * (f⁻¹ * f) by ring,
      PowerSeries.inv_mul_cancel _ hf0, mul_one]
  · rw [const_ex1 (const_lg f), hf]

lemma ex1_nsmul {t : PK} (ht : constantCoeff t = 0) (n : ℕ) : ex1 ((n : KK) • t) = ex1 t ^ n := by
  have hnt : constantCoeff ((n : KK) • t) = 0 := by simp [smul_eq_C_mul, ht]
  apply eq_of_ld1_eq (by rw [const_ex1 hnt]; exact one_ne_zero)
    (by rw [map_pow, const_ex1 ht]; simp)
  · rw [E1_ex1 hnt, E1_pow, E1_ex1 ht, E1_smul, smul_eq_C_mul, smul_eq_C_mul]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      rw [show ((n + 1 : ℕ) : PK) = C ((n + 1 : ℕ) : KK) by simp]
      ring
  · rw [const_ex1 hnt, map_pow, const_ex1 ht, one_pow]

/-! Taylor identity. -/

/-- `θ^k A` where `θ = X d/dX`, i.e. coefficients multiplied by `n^k`. -/
noncomputable def thk (k : ℕ) (A : PK) : PK := mk fun n => (n : KK) ^ k * coeff n A

lemma thk_succ (k : ℕ) (A : PK) : thk (k + 1) A = E1 (thk k A) := by
  ext n; simp [thk, coeff_E1, pow_succ]; ring

lemma thk_zero (A : PK) : thk 0 A = A := by ext n; simp [thk]

lemma taylor (A : PK) {w t : PK} (hw : constantCoeff w = 0) (ht : constantCoeff t = 0) (K : ℕ) :
    TQ K (A.subst (w * ex1 t))
      (∑ k ∈ Finset.range (K + 1), C ((k.factorial : KK)⁻¹) * t ^ k * (thk k A).subst w) := by
  have hwe : constantCoeff (w * ex1 t) = 0 := by simp [hw]
  -- left side as a finite sum
  refine (TQ_subst A hwe K).trans ?_
  -- expand each power
  have hpow : ∀ d ∈ Finset.range (K + 1), TQ K (C (coeff d A) * (w * ex1 t) ^ d)
      (∑ k ∈ Finset.range (K + 1),
        C (coeff d A) * w ^ d * (C ((k.factorial : KK)⁻¹) * ((d : KK) ^ k) • t ^ k)) := by
    intro d _
    rw [mul_pow, ← ex1_nsmul ht d, ← Finset.mul_sum, ← mul_assoc]
    apply TQ.mul_left
    have hdt : constantCoeff ((d : KK) • t) = 0 := by simp [smul_eq_C_mul, ht]
    refine (TQ_subst _ hdt K).trans (TQ_of_coeff (fun n _ => ?_))
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [coeff_exp, smul_pow]
    simp [smul_eq_C_mul, mul_comm, mul_assoc]
  refine (TQ.sum _ _ _ hpow).trans ?_
  rw [Finset.sum_comm]
  apply TQ.sum
  intro k _
  -- ∑_d a_d w^d (1/k!) d^k t^k ≡ (1/k!) t^k (θ^k A)(w)
  have : ∑ d ∈ Finset.range (K + 1),
      C (coeff d A) * w ^ d * (C ((k.factorial : KK)⁻¹) * ((d : KK) ^ k) • t ^ k) =
      C ((k.factorial : KK)⁻¹) * t ^ k *
        ∑ d ∈ Finset.range (K + 1), C (coeff d (thk k A)) * w ^ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [thk, coeff_mk, smul_eq_C_mul, map_mul]
    ring
  rw [this]
  exact TQ.mul_left _ (TQ_subst _ hw K).symm

end A094061
