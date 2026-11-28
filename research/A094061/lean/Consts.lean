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

lemma pow_sub_one_div_sum {c y : KK} (hc0 : c ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    ((1 + c * y) ^ m - 1) / (c * m) = ∑ j ∈ Finset.range m,
      (((m - 1).choose j : ℕ) : KK) * (c ^ j / ((j + 1 : ℕ) : KK)) * y ^ (j + 1) := by
  have hm0 : (m : KK) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
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

section consts2
variable {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h3 : ¬ 3 ∣ p)
include hp

/-- Second-order congruence: `((1 + c b)^k - 1)/(c k) ≡ b mod c` for `c = p m`. -/
lemma K3 (hp5 : 5 ≤ p) {m : ℕ} (hm : 1 ≤ m) {b : KK} (hb : OI p b) {k : ℕ} (hk : 1 ≤ k) :
    OI p ((((1 + ((p * m : ℕ) : KK) * b) ^ k - 1) / (((p * m : ℕ) : KK) * k) - b)
      / ((p * m : ℕ) : KK)) := by
  set c : KK := ((p * m : ℕ) : KK) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast Nat.mul_ne_zero hp.ne_zero (by omega)
  rw [pow_sub_one_div_sum hc0 hk]
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hsplit : ∑ j ∈ Finset.range (q + 1), (((q + 1 - 1).choose j : ℕ) : KK) *
      (c ^ j / ((j + 1 : ℕ) : KK)) * b ^ (j + 1) = (∑ j ∈ Finset.range q,
      (((q + 1 - 1).choose (j + 1) : ℕ) : KK) * (c ^ (j + 1) / ((j + 1 + 1 : ℕ) : KK)) * b ^ (j + 1 + 1)) + b := by
    rw [Finset.sum_range_succ']; congr 1; simp
  rw [hsplit, add_sub_cancel_right, Finset.sum_div]
  apply OI_sum hp
  intro j _
  have e : (((q + 1 - 1).choose (j + 1) : ℕ) : KK) * (c ^ (j + 1) / ((j + 1 + 1 : ℕ) : KK))
      * b ^ (j + 1 + 1) / c = (((q + 1 - 1).choose (j + 1) : ℕ) : KK)
      * (c ^ j / ((j + 2 : ℕ) : KK)) * b ^ (j + 2) := by
    have h2 : ((j + 2 : ℕ) : KK) ≠ 0 := by exact_mod_cast (j + 1).succ_ne_zero
    rw [pow_succ]; push_cast at h2 ⊢; rw [show (j : KK) + 1 + 1 = j + 2 by ring]; field_simp
  rw [e]
  refine OI_mul hp (OI_mul hp (OI_nat hp _) ?_) (OI_pow hp hb _)
  have : c ^ j / ((j + 2 : ℕ) : KK) = rr ((p : ℚ) ^ (j + 2 - 2) / ((j + 2 : ℕ) : ℚ)) * (m : KK) ^ j := by
    rw [show j + 2 - 2 = j by omega, hc]; simp only [rr, map_div₀, map_pow, map_natCast]; push_cast
    ring
  rw [this]
  exact OI_mul hp (OI_rat hp (pint_pj2 hp hp5 (by omega))) (OI_pow hp (OI_nat hp m) j)

lemma OI_rho_pow {κ : KK} (hκ : OI p κ) (hκi : OI p κ⁻¹) (hκ0 : κ ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    OI p ((rho h3 κ ^ m - 1) / ((p : KK) * m)) := by
  rw [rho_eq_one_add hp h3 hκ hκi hκ0]
  exact OI_pow_sub_one_div hp (OI_rho_part hp h3 hκ hκi) hm
    (fun j hj _ => by
      have := OI_rat hp (pint_ppow_div hp hj); simpa [rr] using this) (pKK_ne hp)

lemma OI_UK {κ : KK} (hκ : OI p κ) (hκi : OI p κ⁻¹) (hκ0 : κ ≠ 0) {M : ℕ} (hM : 1 ≤ M) :
    OI p (UK h3 M κ) := by
  have := OI_neg hp (OI_rho_pow hp h3 hκ hκi hκ0 hM)
  rw [UK]; convert this using 1; ring

/-- `U(κ)` satisfies the tangential hypothesis up to degree `N` when every `m ≤ N` divides `M`. -/
theorem tangHyp_UK (hp5 : 5 ≤ p) {κ : KK} (hκ : OI p κ) (hκi : OI p κ⁻¹) (hκ0 : κ ≠ 0)
    (N M : ℕ) (hM1 : 1 ≤ M) (hM : ∀ m, 1 ≤ m → m ≤ N → m ∣ M) : TangHyp h3 κ (UK h3 M κ) N := by
  intro m hm hpm
  have hmN : m ≤ N := le_trans (Nat.le_mul_of_pos_left m hp.pos) hpm
  obtain ⟨k, hk⟩ := hM m hm hmN
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
  set b := (rho h3 κ ^ m - 1) / ((p : KK) * m) with hb
  have hbI : OI p b := OI_rho_pow hp h3 hκ hκi hκ0 hm
  have hpm0 : ((p * m : ℕ) : KK) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hp.ne_zero (by omega)
  have hpK := pKK_ne hp
  have hm0 : (m : KK) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hk0 : (k : KK) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have ha : rho h3 κ ^ m = 1 + ((p * m : ℕ) : KK) * b := by
    rw [hb]; push_cast; field_simp; ring
  have hrhoM : rho h3 κ ^ M = (1 + ((p * m : ℕ) : KK) * b) ^ k := by rw [hk, pow_mul, ha]
  have hsig : sig p h3 κ ^ m = κ ^ (p * m) * rho h3 κ ^ m := by
    rw [rho, mul_pow, ← pow_mul]
    have h1 : κ ^ (p * m) * (κ⁻¹) ^ (p * m) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hκ0, one_pow]
    linear_combination (-(sig p h3 κ) ^ m) * h1
  have key := K3 hp hp5 hm hbI hk1
  have e : (κ ^ (p * m) - sig p h3 κ ^ m - ((p * m : ℕ) : KK) * UK h3 M κ * κ ^ (p * m))
      / ((p * m : ℕ) : KK) ^ 2 = κ ^ (p * m) * ((((1 + ((p * m : ℕ) : KK) * b) ^ k - 1)
        / (((p * m : ℕ) : KK) * k) - b) / ((p * m : ℕ) : KK)) := by
    rw [hsig, UK, hrhoM, ha, hk]
    push_cast
    field_simp
    ring
  rw [e]; exact OI_mul hp (OI_pow hp hκ _) key

omit hp in
lemma UK_mul (M : ℕ) (hp : p.Prime) (hM : 1 ≤ M) (κ κ' : KK) :
    UK h3 M (κ * κ') = UK h3 M κ + UK h3 M κ' - ((p : KK) * M) * (UK h3 M κ * UK h3 M κ') := by
  have hpK := pKK_ne hp
  have hM0 : (M : KK) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [UK, UK, UK, rho_mul, mul_pow]; field_simp; ring

omit hp in
lemma UK_root (M : ℕ) {ζ : KK} (hζ : sig p h3 ζ = ζ ^ p) (hζ0 : ζ ≠ 0) : UK h3 M ζ = 0 := by
  rw [UK, rho, hζ, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow, one_pow, sub_self, zero_div]

end consts2

end A094061
