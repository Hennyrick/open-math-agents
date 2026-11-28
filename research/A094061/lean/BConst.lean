import A094061Dev.Consts

/-!
Explicit constants in `ℚ(ω)` for the branch decomposition (generated; see research/A094061/claude/genbranch.py).
-/

namespace A094061

open PowerSeries

lemma pint_den {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : ℚ) (h : q.den ∣ 36) : pint p q := by
  intro hpd
  have h1 : p ∣ 2 ^ 2 * 3 ^ 2 := by have := dvd_trans hpd h; norm_num at this ⊢; exact this
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega

lemma OI_lit {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℚ) (ha : a.den ∣ 36) (hb : b.den ∣ 36) :
    OI p ((a : KK) + (b : KK) * om) :=
  ⟨a, b, pint_den hp hp5 a ha, pint_den hp hp5 b hb, by simp [rr]⟩

noncomputable def k0 : KK := ((-2/9 : KK) + (-4/9 : KK) * om)

noncomputable def s_z0 : KK := ((1 : KK) + (2 : KK) * om)

noncomputable def s_zr : KK := ((-1/2 : KK) + (-1 : KK) * om)

noncomputable def s_b1 : KK := ((-1/2 : KK) + (1/2 : KK) * om)

noncomputable def s_b2 : KK := ((1 : KK) + (-1 : KK) * om)

noncomputable def s_q1 : KK := ((1 : KK) + (1/2 : KK) * om)

noncomputable def s_q2 : KK := ((-2 : KK) + (-1 : KK) * om)

noncomputable def cb1 : KK := ((1/3 : KK) + (1/3 : KK) * om)

noncomputable def c0b1 : KK := ((-1/3 : KK) + (1/3 : KK) * om)

noncomputable def crb1 : KK := ((2/3 : KK) + (1/3 : KK) * om)

noncomputable def cb2 : KK := ((-2/3 : KK) + (-2/3 : KK) * om)

noncomputable def c0b2 : KK := ((-4/3 : KK) + (-2/3 : KK) * om)

noncomputable def crb2 : KK := ((-1/3 : KK) + (-2/3 : KK) * om)

noncomputable def cq1 : KK := ((0 : KK) + (-1/3 : KK) * om)

noncomputable def c0q1 : KK := ((-2/3 : KK) + (-1/3 : KK) * om)

noncomputable def crq1 : KK := ((1/3 : KK) + (-1/3 : KK) * om)

noncomputable def cq2 : KK := ((0 : KK) + (2/3 : KK) * om)

noncomputable def c0q2 : KK := ((-2/3 : KK) + (2/3 : KK) * om)

noncomputable def crq2 : KK := ((1/3 : KK) + (2/3 : KK) * om)

lemma OI_k0 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p k0 := by
  have := OI_lit hp hp5 (-2/9) (-4/9) (by norm_num) (by norm_num); simpa [k0] using this

lemma OI_s_z0 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p s_z0 := by
  have := OI_lit hp hp5 (1) (2) (by norm_num) (by norm_num); simpa [s_z0] using this

lemma OI_s_zr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p s_zr := by
  have := OI_lit hp hp5 (-1/2) (-1) (by norm_num) (by norm_num); simpa [s_zr] using this

lemma OI_s_b1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p s_b1 := by
  have := OI_lit hp hp5 (-1/2) (1/2) (by norm_num) (by norm_num); simpa [s_b1] using this

lemma OI_s_b2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p s_b2 := by
  have := OI_lit hp hp5 (1) (-1) (by norm_num) (by norm_num); simpa [s_b2] using this

lemma OI_s_q1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p s_q1 := by
  have := OI_lit hp hp5 (1) (1/2) (by norm_num) (by norm_num); simpa [s_q1] using this

lemma OI_s_q2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p s_q2 := by
  have := OI_lit hp hp5 (-2) (-1) (by norm_num) (by norm_num); simpa [s_q2] using this

lemma OI_cb1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cb1 := by
  have := OI_lit hp hp5 (1/3) (1/3) (by norm_num) (by norm_num); simpa [cb1] using this

lemma OI_c0b1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0b1 := by
  have := OI_lit hp hp5 (-1/3) (1/3) (by norm_num) (by norm_num); simpa [c0b1] using this

lemma OI_crb1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crb1 := by
  have := OI_lit hp hp5 (2/3) (1/3) (by norm_num) (by norm_num); simpa [crb1] using this

lemma OI_cb2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cb2 := by
  have := OI_lit hp hp5 (-2/3) (-2/3) (by norm_num) (by norm_num); simpa [cb2] using this

lemma OI_c0b2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0b2 := by
  have := OI_lit hp hp5 (-4/3) (-2/3) (by norm_num) (by norm_num); simpa [c0b2] using this

lemma OI_crb2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crb2 := by
  have := OI_lit hp hp5 (-1/3) (-2/3) (by norm_num) (by norm_num); simpa [crb2] using this

lemma OI_cq1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cq1 := by
  have := OI_lit hp hp5 (0) (-1/3) (by norm_num) (by norm_num); simpa [cq1] using this

lemma OI_c0q1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0q1 := by
  have := OI_lit hp hp5 (-2/3) (-1/3) (by norm_num) (by norm_num); simpa [c0q1] using this

lemma OI_crq1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crq1 := by
  have := OI_lit hp hp5 (1/3) (-1/3) (by norm_num) (by norm_num); simpa [crq1] using this

lemma OI_cq2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cq2 := by
  have := OI_lit hp hp5 (0) (2/3) (by norm_num) (by norm_num); simpa [cq2] using this

lemma OI_c0q2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0q2 := by
  have := OI_lit hp hp5 (-2/3) (2/3) (by norm_num) (by norm_num); simpa [c0q2] using this

lemma OI_crq2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crq2 := by
  have := OI_lit hp hp5 (1/3) (2/3) (by norm_num) (by norm_num); simpa [crq2] using this

lemma k0_mul_inv : k0 * ((3/2 : KK) + (3 : KK) * om) = 1 := by
  rw [k0]; linear_combination ((-4/3 : KK) * om ^ 0) * om_rel

lemma k0_ne : k0 ≠ 0 := fun h => by have := k0_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_k0_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p k0⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right k0_mul_inv]
  have := OI_lit hp hp5 (3/2) (3) (by norm_num) (by norm_num); simpa using this

lemma cb1_mul_inv : cb1 * ((0 : KK) + (-3 : KK) * om) = 1 := by
  rw [cb1]; linear_combination ((-1 : KK) * om ^ 0) * om_rel

lemma cb1_ne : cb1 ≠ 0 := fun h => by have := cb1_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_cb1_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cb1⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right cb1_mul_inv]
  have := OI_lit hp hp5 (0) (-3) (by norm_num) (by norm_num); simpa using this

lemma c0b1_mul_inv : c0b1 * ((-2 : KK) + (-1 : KK) * om) = 1 := by
  rw [c0b1]; linear_combination ((-1/3 : KK) * om ^ 0) * om_rel

lemma c0b1_ne : c0b1 ≠ 0 := fun h => by have := c0b1_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_c0b1_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0b1⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right c0b1_mul_inv]
  have := OI_lit hp hp5 (-2) (-1) (by norm_num) (by norm_num); simpa using this

lemma crb1_mul_inv : crb1 * ((1 : KK) + (-1 : KK) * om) = 1 := by
  rw [crb1]; linear_combination ((-1/3 : KK) * om ^ 0) * om_rel

lemma crb1_ne : crb1 ≠ 0 := fun h => by have := crb1_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_crb1_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crb1⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right crb1_mul_inv]
  have := OI_lit hp hp5 (1) (-1) (by norm_num) (by norm_num); simpa using this

lemma cb2_mul_inv : cb2 * ((0 : KK) + (3/2 : KK) * om) = 1 := by
  rw [cb2]; linear_combination ((-1 : KK) * om ^ 0) * om_rel

lemma cb2_ne : cb2 ≠ 0 := fun h => by have := cb2_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_cb2_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cb2⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right cb2_mul_inv]
  have := OI_lit hp hp5 (0) (3/2) (by norm_num) (by norm_num); simpa using this

lemma c0b2_mul_inv : c0b2 * ((-1/2 : KK) + (1/2 : KK) * om) = 1 := by
  rw [c0b2]; linear_combination ((-1/3 : KK) * om ^ 0) * om_rel

lemma c0b2_ne : c0b2 ≠ 0 := fun h => by have := c0b2_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_c0b2_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0b2⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right c0b2_mul_inv]
  have := OI_lit hp hp5 (-1/2) (1/2) (by norm_num) (by norm_num); simpa using this

lemma crb2_mul_inv : crb2 * ((1 : KK) + (2 : KK) * om) = 1 := by
  rw [crb2]; linear_combination ((-4/3 : KK) * om ^ 0) * om_rel

lemma crb2_ne : crb2 ≠ 0 := fun h => by have := crb2_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_crb2_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crb2⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right crb2_mul_inv]
  have := OI_lit hp hp5 (1) (2) (by norm_num) (by norm_num); simpa using this

lemma cq1_mul_inv : cq1 * ((3 : KK) + (3 : KK) * om) = 1 := by
  rw [cq1]; linear_combination ((-1 : KK) * om ^ 0) * om_rel

lemma cq1_ne : cq1 ≠ 0 := fun h => by have := cq1_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_cq1_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cq1⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right cq1_mul_inv]
  have := OI_lit hp hp5 (3) (3) (by norm_num) (by norm_num); simpa using this

lemma c0q1_mul_inv : c0q1 * ((-1 : KK) + (1 : KK) * om) = 1 := by
  rw [c0q1]; linear_combination ((-1/3 : KK) * om ^ 0) * om_rel

lemma c0q1_ne : c0q1 ≠ 0 := fun h => by have := c0q1_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_c0q1_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0q1⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right c0q1_mul_inv]
  have := OI_lit hp hp5 (-1) (1) (by norm_num) (by norm_num); simpa using this

lemma crq1_mul_inv : crq1 * ((2 : KK) + (1 : KK) * om) = 1 := by
  rw [crq1]; linear_combination ((-1/3 : KK) * om ^ 0) * om_rel

lemma crq1_ne : crq1 ≠ 0 := fun h => by have := crq1_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_crq1_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crq1⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right crq1_mul_inv]
  have := OI_lit hp hp5 (2) (1) (by norm_num) (by norm_num); simpa using this

lemma cq2_mul_inv : cq2 * ((-3/2 : KK) + (-3/2 : KK) * om) = 1 := by
  rw [cq2]; linear_combination ((-1 : KK) * om ^ 0) * om_rel

lemma cq2_ne : cq2 ≠ 0 := fun h => by have := cq2_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_cq2_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p cq2⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right cq2_mul_inv]
  have := OI_lit hp hp5 (-3/2) (-3/2) (by norm_num) (by norm_num); simpa using this

lemma c0q2_mul_inv : c0q2 * ((-1 : KK) + (-1/2 : KK) * om) = 1 := by
  rw [c0q2]; linear_combination ((-1/3 : KK) * om ^ 0) * om_rel

lemma c0q2_ne : c0q2 ≠ 0 := fun h => by have := c0q2_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_c0q2_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p c0q2⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right c0q2_mul_inv]
  have := OI_lit hp hp5 (-1) (-1/2) (by norm_num) (by norm_num); simpa using this

lemma crq2_mul_inv : crq2 * ((-1 : KK) + (-2 : KK) * om) = 1 := by
  rw [crq2]; linear_combination ((-4/3 : KK) * om ^ 0) * om_rel

lemma crq2_ne : crq2 ≠ 0 := fun h => by have := crq2_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this

lemma OI_crq2_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p crq2⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right crq2_mul_inv]
  have := OI_lit hp hp5 (-1) (-2) (by norm_num) (by norm_num); simpa using this

lemma cb1_eq : cb1 = s_b1 * k0 := by
  simp only [cb1, s_b1, k0]; linear_combination ((2/9 : KK) * om ^ 0) * om_rel

lemma c0b1_eq : c0b1 = (s_b1 - s_z0) * k0 := by
  simp only [c0b1, s_b1, s_z0, k0]; linear_combination ((-2/3 : KK) * om ^ 0) * om_rel

lemma crb1_eq : crb1 = (s_b1 - s_zr) * k0 := by
  simp only [crb1, s_b1, s_zr, k0]; linear_combination ((2/3 : KK) * om ^ 0) * om_rel

lemma cb2_eq : cb2 = s_b2 * k0 := by
  simp only [cb2, s_b2, k0]; linear_combination ((-4/9 : KK) * om ^ 0) * om_rel

lemma c0b2_eq : c0b2 = (s_b2 - s_z0) * k0 := by
  simp only [c0b2, s_b2, s_z0, k0]; linear_combination ((-4/3 : KK) * om ^ 0) * om_rel

lemma crb2_eq : crb2 = (s_b2 - s_zr) * k0 := by
  simp only [crb2, s_b2, s_zr, k0]; linear_combination ((0 : KK)) * om_rel

lemma cq1_eq : cq1 = s_q1 * k0 := by
  simp only [cq1, s_q1, k0]; linear_combination ((2/9 : KK) * om ^ 0) * om_rel

lemma c0q1_eq : c0q1 = (s_q1 - s_z0) * k0 := by
  simp only [c0q1, s_q1, s_z0, k0]; linear_combination ((-2/3 : KK) * om ^ 0) * om_rel

lemma crq1_eq : crq1 = (s_q1 - s_zr) * k0 := by
  simp only [crq1, s_q1, s_zr, k0]; linear_combination ((2/3 : KK) * om ^ 0) * om_rel

lemma cq2_eq : cq2 = s_q2 * k0 := by
  simp only [cq2, s_q2, k0]; linear_combination ((-4/9 : KK) * om ^ 0) * om_rel

lemma c0q2_eq : c0q2 = (s_q2 - s_z0) * k0 := by
  simp only [c0q2, s_q2, s_z0, k0]; linear_combination ((-4/3 : KK) * om ^ 0) * om_rel

lemma crq2_eq : crq2 = (s_q2 - s_zr) * k0 := by
  simp only [crq2, s_q2, s_zr, k0]; linear_combination ((0 : KK)) * om_rel

lemma root_b1 : c0b1 * crb1 = om * cb1 := by
  simp only [c0b1, crb1, cb1]; linear_combination ((-2/9 : KK) * om ^ 0) * om_rel

lemma root_b2 : c0b2 * crb2 = (-1 - om) * cb2 := by
  simp only [c0b2, crb2, cb2]; linear_combination ((-2/9 : KK) * om ^ 0) * om_rel

lemma root_q1 : c0q1 * crq1 = (-1 - om) * cq1 := by
  simp only [c0q1, crq1, cq1]; linear_combination ((-2/9 : KK) * om ^ 0) * om_rel

lemma root_q2 : c0q2 * crq2 = om * cq2 := by
  simp only [c0q2, crq2, cq2]; linear_combination ((-2/9 : KK) * om ^ 0) * om_rel

lemma root_0 : c0b1 * c0b2 = 1 * (c0q1 * c0q2) := by
  simp only [c0b1, c0b2, c0q1, c0q2]; linear_combination ((0 : KK)) * om_rel

lemma root_r : crb1 * crb2 = (-1 - om) * (crq1 * crq2) := by
  simp only [crb1, crb2, crq1, crq2]; linear_combination ((-1/9 : KK) * om ^ 0 + (-2/9 : KK) * om ^ 1) * om_rel


end A094061
