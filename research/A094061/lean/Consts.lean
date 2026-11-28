import A094061Dev.Tang3

/-!
Log-free constants `U(κ) = (1 - ρ^M) / (p M)`, `ρ = σ(κ) / κ^p`.
-/

namespace A094061

open PowerSeries

lemma aux_five (v : ℕ) (hv : 1 ≤ v) : v + 2 ≤ 5 ^ v := by
  induction v with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have := ih h; rw [pow_succ]; omega

/-- `p^(j-2)/j` is `p`-integral for `j ≥ 2`, `p ≥ 5`. -/
lemma pint_pj2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {j : ℕ} (hj : 2 ≤ j) :
    pint p ((p : ℚ) ^ (j - 2) / j) := by
  obtain ⟨v, u, hu, hfac⟩ : ∃ v u, ¬ p ∣ u ∧ j = p ^ v * u :=
    ⟨j.factorization p, ordCompl[p] j, Nat.not_dvd_ordCompl hp (by omega),
      (Nat.ordProj_mul_ordCompl_eq_self j p).symm⟩
  have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (by rintro rfl; simp at hfac; omega)
  have hpv : p ^ v ≤ j := by rw [hfac]; exact Nat.le_mul_of_pos_right _ hu1
  have hv : v ≤ j - 2 := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · omega
    · have h1 := aux_five v hpos
      have h2 : 5 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp5 v
      omega
  have hu0 : (u : ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : ℚ) ^ (j - 2) / j = ((p ^ (j - 2 - v) : ℕ) : ℚ) * (u : ℚ)⁻¹ := by
    rw [show (j : ℚ) = (p : ℚ) ^ v * u by exact_mod_cast hfac]
    push_cast
    rw [show (p : ℚ) ^ (j - 2) = (p : ℚ) ^ (j - 2 - v) * (p : ℚ) ^ v by
      rw [← pow_add, Nat.sub_add_cancel hv]]
    field_simp
  rw [e]; exact pint_mul hp (pint_nat hp _) (pint_inv_nat hp hu)

section consts
variable {p : ℕ} (hp : p.Prime)
include hp

/-- `((1 + c y)^m - 1)/(c m)` is integral when `c^(j-1)/j` is integral for all `j ≥ 1`. -/
lemma OI_pow_sub_one_div {c y : KK} (hy : OI p y) {m : ℕ} (hm : 1 ≤ m)
    (hc : ∀ j, 1 ≤ j → j ≤ m → OI p (c ^ (j - 1) / j)) (hc0 : c ≠ 0) :
    OI p (((1 + c * y) ^ m - 1) / (c * m)) := by
  have hm0 : (m : KK) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have e : ((1 + c * y) ^ m - 1) / (c * m) = ∑ j ∈ Finset.range m,
      (((m - 1).choose j : ℕ) : KK) * (c ^ j / ((j + 1 : ℕ) : KK)) * y ^ (j + 1) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
    rw [Finset.sum_div]
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hch : ((q + 1).choose (j + 1) : KK) * ((j + 1 : ℕ) : KK) = ((q + 1 : ℕ) : KK) * (q.choose j : KK) := by
      have := Nat.add_one_mul_choose_eq q j
      exact_mod_cast this.symm
    have hj : ((j + 1 : ℕ) : KK) ≠ 0 := by exact_mod_cast j.succ_ne_zero
    have key : ((q + 1).choose (j + 1) : KK) = ((q + 1 : ℕ) : KK) * (q.choose j : KK) / ((j + 1 : ℕ) : KK) := by
      rw [eq_div_iff hj]; exact hch
    rw [key, mul_pow, pow_succ c j]
    field_simp
  rw [e]
  apply OI_sum hp
  intro j hj
  simp at hj
  refine OI_mul hp (OI_mul hp (OI_nat hp _) ?_) (OI_pow hp hy _)
  have := hc (j + 1) (by omega) (by omega)
  simpa using this

variable (h3 : ¬ 3 ∣ p)

/-- `ρ(κ) = σ(κ) / κ^p`. -/
noncomputable def rho (κ : KK) : KK := sig p h3 κ * (κ⁻¹) ^ p

/-- `U(κ) = (1 - ρ^M)/(p M)`. -/
noncomputable def UK (M : ℕ) (κ : KK) : KK := (1 - rho h3 κ ^ M) / ((p : KK) * M)

omit hp in
lemma rho_mul (κ κ' : KK) : rho h3 (κ * κ') = rho h3 κ * rho h3 κ' := by
  simp only [rho, map_mul, mul_inv, mul_pow]; ring

lemma rho_eq_one_add {κ : KK} (hκ : OI p κ) (hκi : OI p κ⁻¹) (hκ0 : κ ≠ 0) :
    rho h3 κ = 1 + (p : KK) * ((sig p h3 κ - κ ^ p) / p * (κ⁻¹) ^ p) := by
  rw [rho]
  have h1 : (κ⁻¹) ^ p * κ ^ p = 1 := by rw [← mul_pow, inv_mul_cancel₀ hκ0, one_pow]
  field_simp [pKK_ne hp]
  linear_combination h1

lemma OI_rho_part {κ : KK} (hκ : OI p κ) (hκi : OI p κ⁻¹) :
    OI p ((sig p h3 κ - κ ^ p) / p * (κ⁻¹) ^ p) :=
  OI_mul hp (frob_cong hp h3 hκ) (OI_pow hp hκi p)

end consts

end A094061
