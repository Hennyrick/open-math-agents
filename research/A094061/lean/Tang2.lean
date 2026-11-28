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

lemma E1_sum {ι : Type*} (s : Finset ι) (f : ι → PK) : E1 (∑ i ∈ s, f i) = ∑ i ∈ s, E1 (f i) := by
  simp only [E1, map_sum, Finset.mul_sum]

/-- `(-p)^k / k!`. -/
noncomputable def aa (p k : ℕ) : KK := (-(p : KK)) ^ k / (k.factorial : KK)

lemma aa_rel {p : ℕ} (hp : p.Prime) (k : ℕ) :
    aa p (k + 2) / (p : KK) ^ 2 * ((k + 2 : ℕ) : KK) = -(aa p (k + 1) / p) := by
  have hpK := pKK_ne hp
  simp only [aa, Nat.factorial_succ]
  push_cast
  have h1 : ((k + 1).factorial : KK) ≠ 0 := by exact_mod_cast (k + 1).factorial_ne_zero
  have h2 : ((k : KK) + 1 + 1) ≠ 0 := by
    have : ((k + 2 : ℕ) : KK) ≠ 0 := by exact_mod_cast (k + 1).succ_ne_zero
    push_cast at this; rw [show (k : KK) + 1 + 1 = k + 2 by ring]; exact this
  rw [Nat.factorial_succ] at h1; push_cast at h1
  field_simp
  ring

lemma aa_one (p : ℕ) : aa p 1 = -(p : KK) := by simp [aa]

lemma Cq_p {p : ℕ} (hp : p.Prime) : C ((p : KK)⁻¹) * ((p : PK)) = 1 := by
  rw [← map_natCast C p, ← map_mul, inv_mul_cancel₀ (pKK_ne hp), map_one]

lemma E1_Cmul (c : KK) (A : PK) : E1 (C c * A) = C c * E1 A := by
  rw [E1_mul, E1_C]; ring

section identity
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ Uc : KK) (u : PK) (hu1 : constantCoeff u = 1)

/-- `R_j(w)`. -/
noncomputable def RR (j : ℕ) : PK := (thk j Li2).subst (ww h3 κ u)

noncomputable def H1 : PK := Li2.subst (ff κ u) - C (((p : KK) ^ 2)⁻¹) * Li2.subst (ww h3 κ u)
  - C Uc * (thk 1 Li2).subst (ff κ u)

noncomputable def H2 : PK := UU hp h3 u * (-(thk 1 Li2).subst (ff κ u)
  + C ((p : KK)⁻¹) * (thk 1 Li2).subst (ww h3 κ u))

noncomputable def H3 (N : ℕ) : PK := -∑ k ∈ Finset.range N,
  C (aa p (k + 2) / (p : KK) ^ 2) * UU hp h3 u ^ (k + 2) * RR h3 κ u (k + 2)

/-- The truncated Taylor sum. -/
noncomputable def SS (N : ℕ) : PK :=
  ∑ k ∈ Finset.range (N + 2), C (aa p k) * UU hp h3 u ^ k * RR h3 κ u (k + 1)

/-- The pairing with the Taylor sum in place of `Li₁(w e^t)`. -/
noncomputable def Ep' (N : ℕ) : PK :=
  (C Uc + UU hp h3 u) * (-(ell u * (thk 2 Li2).subst (ff κ u)))
  - (-(thk 1 Li2).subst (ff κ u) + C ((p : KK)⁻¹) * SS hp h3 κ u N) * (ell u - E1 (UU hp h3 u))

include hp hu1

lemma E1_Li2_ff : E1 (Li2.subst (ff κ u)) = ell u * (thk 1 Li2).subst (ff κ u) := by
  rw [E1_subst' _ (const_ff κ u) (E1_ff κ u hu1), show thk 1 Li2 = E1 Li2 by
    rw [thk_succ, thk_zero]]

lemma E1_thk_ff (j : ℕ) : E1 ((thk j Li2).subst (ff κ u)) = ell u * (thk (j + 1) Li2).subst (ff κ u) := by
  rw [E1_subst' _ (const_ff κ u) (E1_ff κ u hu1), thk_succ]

lemma E1_Li2_ww : E1 (Li2.subst (ww h3 κ u)) = ((p : PK) * ell u) * RR h3 κ u 1 := by
  rw [E1_subst' _ (const_ww h3 κ u hp.ne_zero) (E1_ww h3 κ u hu1), RR, show thk 1 Li2 = E1 Li2 by
    rw [thk_succ, thk_zero]]

lemma E1_RR (j : ℕ) : E1 (RR h3 κ u j) = ((p : PK) * ell u) * RR h3 κ u (j + 1) := by
  rw [RR, RR, E1_subst' _ (const_ww h3 κ u hp.ne_zero) (E1_ww h3 κ u hu1), thk_succ]

lemma E1_H3 (N : ℕ) : E1 (H3 hp h3 κ u N) =
    ∑ k ∈ Finset.range N, C (aa p (k + 1) / p) * UU hp h3 u ^ (k + 1) * E1 (UU hp h3 u)
      * RR h3 κ u (k + 2)
    - C ((p : KK)⁻¹) * ell u * ∑ k ∈ Finset.range N,
      C (aa p (k + 2)) * UU hp h3 u ^ (k + 2) * RR h3 κ u (k + 3) := by
  have hpK := pKK_ne hp
  rw [H3, E1_neg, E1_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [E1_mul, E1_mul, E1_C, E1_pow, E1_RR hp h3 κ u hu1]
  have e := aa_rel hp k
  have e2 : C (aa p (k + 2) / (p : KK) ^ 2) * ((p : PK)) = C ((p : KK)⁻¹) * C (aa p (k + 2)) := by
    rw [show ((p : PK)) = C (p : KK) by simp, ← map_mul, ← map_mul]; congr 1; field_simp
  have e3 : C (aa p (k + 2) / (p : KK) ^ 2) * ((k + 2 : ℕ) : PK) = -C (aa p (k + 1) / p) := by
    rw [← map_natCast C (k + 2), ← map_mul, e, map_neg]
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by omega]
  linear_combination (-(UU hp h3 u ^ (k + 2) * ell u * RR h3 κ u (k + 3))) * e2
    - (UU hp h3 u ^ (k + 1) * E1 (UU hp h3 u) * RR h3 κ u (k + 2)) * e3

lemma sum_shift (N : ℕ) :
    ∑ k ∈ Finset.range N, C (aa p (k + 1) / p) * UU hp h3 u ^ (k + 1) * E1 (UU hp h3 u)
      * RR h3 κ u (k + 2) =
    C (aa p 1 / p) * UU hp h3 u * E1 (UU hp h3 u) * RR h3 κ u 2
    + C ((p : KK)⁻¹) * E1 (UU hp h3 u) * ∑ k ∈ Finset.range N,
      C (aa p (k + 2)) * UU hp h3 u ^ (k + 2) * RR h3 κ u (k + 3)
    - C (aa p (N + 1) / p) * UU hp h3 u ^ (N + 1) * E1 (UU hp h3 u) * RR h3 κ u (N + 2) := by
  set g : ℕ → PK := fun j => C (aa p j / p) * UU hp h3 u ^ j * E1 (UU hp h3 u) * RR h3 κ u (j + 1)
  have h1 := Finset.sum_range_succ (fun k => g (k + 1)) N
  have h2 := Finset.sum_range_succ' (fun k => g (k + 1)) N
  have h3' : ∑ k ∈ Finset.range N, g (k + 2) = C ((p : KK)⁻¹) * E1 (UU hp h3 u) *
      ∑ k ∈ Finset.range N, C (aa p (k + 2)) * UU hp h3 u ^ (k + 2) * RR h3 κ u (k + 3) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [g, div_eq_inv_mul, map_mul]; ring
  simp only [g] at h1 h2 h3'
  simp only [add_assoc, Nat.reduceAdd, pow_one, zero_add] at h1 h2 h3'
  linear_combination h2 - h1 + h3'

lemma SS_split (N : ℕ) : SS hp h3 κ u N = RR h3 κ u 1 + C (aa p 1) * UU hp h3 u * RR h3 κ u 2
    + ∑ k ∈ Finset.range N, C (aa p (k + 2)) * UU hp h3 u ^ (k + 2) * RR h3 κ u (k + 3) := by
  rw [SS, Finset.sum_range_succ', Finset.sum_range_succ']
  simp [aa]; ring

lemma E1_H1 : E1 (H1 h3 κ Uc u) = ell u * (thk 1 Li2).subst (ff κ u)
    - C ((p : KK)⁻¹) * ell u * RR h3 κ u 1 - C Uc * ell u * (thk 2 Li2).subst (ff κ u) := by
  rw [H1, E1_sub, E1_sub, E1_Cmul, E1_Cmul, E1_Li2_ff hp κ u hu1, E1_Li2_ww hp h3 κ u hu1,
    E1_thk_ff hp κ u hu1 1]
  have e : C (((p : KK) ^ 2)⁻¹) * ((p : PK)) = C ((p : KK)⁻¹) := by
    rw [← map_natCast C p, ← map_mul]; congr 1; field_simp [pKK_ne hp]
  linear_combination (-(ell u * RR h3 κ u 1)) * e

lemma E1_H2 : E1 (H2 hp h3 κ u) = E1 (UU hp h3 u) * (-(thk 1 Li2).subst (ff κ u)
    + C ((p : KK)⁻¹) * RR h3 κ u 1) + UU hp h3 u * (-(ell u * (thk 2 Li2).subst (ff κ u))
    + ell u * RR h3 κ u 2) := by
  rw [H2, show (thk 1 Li2).subst (ww h3 κ u) = RR h3 κ u 1 from rfl, E1_mul, E1_add, E1_neg,
    E1_Cmul, E1_thk_ff hp κ u hu1 1, E1_RR hp h3 κ u hu1 1]
  have e := Cq_p hp
  linear_combination (UU hp h3 u * ell u * RR h3 κ u 2) * e

/-- Claim B: the derivative of `H` is the Taylor-truncated pairing up to a boundary term. -/
lemma main_identity (N : ℕ) :
    E1 (H1 h3 κ Uc u + H2 hp h3 κ u + H3 hp h3 κ u N) = Ep' hp h3 κ Uc u N
      - C (aa p (N + 1) / p) * UU hp h3 u ^ (N + 1) * E1 (UU hp h3 u) * RR h3 κ u (N + 2) := by
  rw [E1_add, E1_add, E1_H1 hp h3 κ Uc u hu1, E1_H2 hp h3 κ u hu1, E1_H3 hp h3 κ u hu1,
    sum_shift hp h3 κ u hu1, Ep', SS_split hp h3 κ u hu1, aa_one p]
  have h1 : C (-(p : KK) / p) = -1 := by
    rw [show (-(p : KK)) / p = -1 by field_simp [pKK_ne hp], map_neg, map_one]
  have h2 : C ((p : KK)⁻¹) * C (-(p : KK)) = -1 := by
    rw [← map_mul, mul_neg, inv_mul_cancel₀ (pKK_ne hp), map_neg, map_one]
  rw [h1]
  linear_combination (UU hp h3 u * RR h3 κ u 2 * ell u
    - UU hp h3 u * RR h3 κ u 2 * E1 (UU hp h3 u)) * h2

end identity

end A094061
