import A094061Dev.Branch

/-!
The core proposition: `U(Y)` is an Euler derivative of an integral series.
-/

namespace A094061

open PowerSeries

section algebra
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p)
include hp

lemma UU_mul {a b : PK} (ha : constantCoeff a ≠ 0) (hb : constantCoeff b ≠ 0) :
    UU hp h3 (a * b) = UU hp h3 a + UU hp h3 b := by
  simp only [UU, lg_mul ha hb, map_add, smul_add]; abel

lemma UU_inv {a : PK} (ha : constantCoeff a ≠ 0) : UU hp h3 a⁻¹ = -UU hp h3 a := by
  simp only [UU, lg_inv ha, map_neg, smul_neg]; abel

omit hp in
lemma ld1_C (c : KK) : ld1 (C c) = 0 := by rw [ld1, E1_C, zero_mul]

omit hp in
lemma lg_C (c : KK) : lg (C c) = 0 := by
  apply eq_of_E1_eq
  · rw [E1_lg, ld1_C]; simp [E1]
  · simp [const_lg]

lemma UU_C_mul {c : KK} (hc : c ≠ 0) {a : PK} (ha : constantCoeff a ≠ 0) :
    UU hp h3 (C c * a) = UU hp h3 a := by
  rw [UU_mul hp h3 (by simpa using hc) ha]
  simp [UU, lg_C]

end algebra

lemma const_uu_ne (s : KK) : constantCoeff (uu s) ≠ 0 := by rw [const_uu]; exact one_ne_zero

lemma one_sub_ff_b {sb cb : KK} (h : cb = sb * k0) : 1 - ff cb w0 = uu sb := by
  rw [ff, vv, uu, Gb_eq', h, map_mul]; ring

lemma one_sub_ff_0b {sb c0b : KK} (h : c0b = (sb - s_z0) * k0) :
    1 - ff c0b (uu s_zr) = uu sb * (uu s_z0)⁻¹ := by
  apply cancel1 (const_uu_ne s_z0)
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (const_uu_ne s_z0), mul_one]
  have hg := Gb_eq'
  simp only [ff, vv, w0] at hg ⊢
  simp only [uu] at hg ⊢
  rw [h, map_mul, map_sub]
  linear_combination (C sb - C s_z0) * hg

lemma one_sub_ff_rb {sb crb : KK} (h : crb = (sb - s_zr) * k0) :
    1 - ff crb (uu s_z0) = uu sb * (uu s_zr)⁻¹ := by
  apply cancel1 (const_uu_ne s_zr)
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (const_uu_ne s_zr), mul_one]
  have hg := Gb_eq'
  simp only [ff, vv, w0] at hg ⊢
  simp only [uu] at hg ⊢
  rw [h, map_mul, map_sub]
  linear_combination (C sb - C s_zr) * hg

section coreb
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p)

/-- `U_α`, `λ_α`, `L_α`. -/
noncomputable def Ua (s : KK) : PK := UU hp h3 (uu s)
noncomputable def la (s : KK) : PK := ld1 (uu s)
noncomputable def La (s : KK) : PK := phi1 p hp.ne_zero h3 (ld1 (uu s))

/-- The `b`-independent term. -/
noncomputable def Wt : PK := Ua hp h3 s_zr * la s_z0 - Ua hp h3 s_z0 * La hp h3 s_zr
  + Ua hp h3 s_z0 * la s_zr - Ua hp h3 s_zr * La hp h3 s_z0

include hp

lemma core_b (sb cb c0b crb Ucb Uc0 Ucr : KK) (h1 : cb = sb * k0) (h2 : c0b = (sb - s_z0) * k0)
    (h3' : crb = (sb - s_zr) * k0) :
    Epair hp h3 c0b Uc0 (uu s_zr) + Epair hp h3 crb Ucr (uu s_z0) - Epair hp h3 cb Ucb w0 =
      C Uc0 * (la sb - la s_z0) + C Ucr * (la sb - la s_zr) - C Ucb * la sb
      + Ua hp h3 s_z0 + Ua hp h3 s_zr - Ua hp h3 sb - Wt hp h3 := by
  have i0 : constantCoeff (uu s_z0)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero (const_uu_ne _)
  have ir : constantCoeff (uu s_zr)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero (const_uu_ne _)
  rw [Epair, Epair, Epair, one_sub_ff_b h1, one_sub_ff_0b h2, one_sub_ff_rb h3']
  simp only [w0,
    UU_mul hp h3 (const_uu_ne _) i0, UU_mul hp h3 (const_uu_ne _) ir,
    UU_mul hp h3 (const_uu_ne _) (const_uu_ne _), UU_inv hp h3 (const_uu_ne _),
    ld1_mul (const_uu_ne _) i0, ld1_mul (const_uu_ne _) ir, ld1_mul (const_uu_ne _) (const_uu_ne _),
    ld1_inv (const_uu_ne _), map_add, Wt, Ua, la, La]
  ring

end coreb

end A094061
