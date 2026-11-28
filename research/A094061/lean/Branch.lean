import A094061Dev.BConst

/-!
The branch `g = m(z) - m0` over `ℚ(ω)`, the units `u_α = 1 - s_α g`, and the branch `Y`.
-/

namespace A094061

open PowerSeries

/-- `F(g) = (1 - s0 g)(1 - sr g)`. -/
noncomputable def Fg (g : PK) : PK := (1 - C s_z0 * g) * (1 - C s_zr * g)

/-- Iterates `g_{k+1} = κ0 z F(g_k)`. -/
noncomputable def Git : ℕ → PK
  | 0 => 0
  | k + 1 => C k0 * X * Fg (Git k)

lemma Fg_sub (a b : PK) : Fg a - Fg b = (a - b) * (C (s_z0 * s_zr) * (a + b) - C s_z0 - C s_zr) := by
  simp only [Fg, map_mul]; ring

lemma Git_step (k : ℕ) : X ^ k ∣ Git k - Git (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨C k0 * q * (C (s_z0 * s_zr) * (Git k + Git (k + 1)) - C s_z0 - C s_zr), ?_⟩
    rw [show Git (k + 1) - Git (k + 1 + 1) = C k0 * X * (Fg (Git k) - Fg (Git (k + 1))) by
      simp only [Git]; ring, Fg_sub, hq]
    ring

lemma Git_stab (k m : ℕ) (h : k ≤ m) : X ^ k ∣ Git k - Git m := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [show Git k - Git (m + 1) = (Git k - Git m) + (Git m - Git (m + 1)) by ring]
    exact dvd_add ih ((pow_dvd_pow X hm).trans (Git_step m))

/-- The branch `g`. -/
noncomputable def Gb : PK := mk fun n => coeff n (Git (n + 1))

lemma TQ_Gb (n : ℕ) : TQ n Gb (Git (n + 1)) := by
  apply TQ_of_coeff
  intro j hj
  rw [Gb, coeff_mk]
  exact TQ_coeff (Git_stab (j + 1) (n + 1) (by omega)) (le_refl j)

lemma Gb_eq : Gb = C k0 * X * Fg Gb := by
  apply eq_of_TQ
  intro n
  refine (TQ_Gb n).trans ?_
  have h1 : TQ n (Git (n + 1)) (Git (n + 2)) := TQ_of_coeff (fun j hj =>
    TQ_coeff (Git_step (n + 1)) (by omega))
  refine h1.trans ?_
  show TQ n (C k0 * X * Fg (Git (n + 1))) (C k0 * X * Fg Gb)
  unfold TQ
  have h2 : X ^ (n + 1) ∣ Git (n + 1) - Gb := by
    have := TQ_Gb n; unfold TQ at this; rw [← neg_sub]; exact (dvd_neg).2 this
  obtain ⟨q, hq⟩ := h2
  refine ⟨C k0 * X * q * (C (s_z0 * s_zr) * (Git (n + 1) + Gb) - C s_z0 - C s_zr) * X ^ 0, ?_⟩
  rw [show C k0 * X * Fg (Git (n + 1)) - C k0 * X * Fg Gb = C k0 * X * (Fg (Git (n + 1)) - Fg Gb) by ring,
    Fg_sub, hq]
  ring

lemma const_Gb : constantCoeff Gb = 0 := by
  rw [Gb_eq]; simp

section integ
variable {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
include hp hp5

lemma OIs_Git (k : ℕ) : OIs p (Git k) := by
  induction k with
  | zero => simpa [Git] using OIs_C hp (OI_zero hp)
  | succ k ih =>
    simp only [Git, Fg]
    exact OIs_mul hp (OIs_mul hp (OIs_C hp (OI_k0 hp hp5)) (OIs_X hp))
      (OIs_mul hp (OIs_sub hp (OIs_one hp) (OIs_mul hp (OIs_C hp (OI_s_z0 hp hp5)) ih))
        (OIs_sub hp (OIs_one hp) (OIs_mul hp (OIs_C hp (OI_s_zr hp hp5)) ih)))

lemma OIs_Gb : OIs p Gb := fun n => by rw [Gb, coeff_mk]; exact OIs_Git hp hp5 (n + 1) n

end integ

/-- `u_α = 1 - s_α g`. -/
noncomputable def uu (s : KK) : PK := 1 - C s * Gb

lemma const_uu (s : KK) : constantCoeff (uu s) = 1 := by simp [uu, const_Gb]

/-- `w0 = u_0 u_r`, so that `g = κ0 z w0`. -/
noncomputable def w0 : PK := uu s_z0 * uu s_zr

lemma Gb_eq' : Gb = C k0 * X * w0 := by
  conv_lhs => rw [Gb_eq]
  rfl

lemma const_w0 : constantCoeff w0 = 1 := by simp [w0, const_uu]

/-- The branch `Y = ω² u_{b1} u_{b2} / (u_{q1} u_{q2})`. -/
noncomputable def Yb : PK := C (om ^ 2) * uu s_b1 * uu s_b2 * (uu s_q1)⁻¹ * (uu s_q2)⁻¹

/-- The defining equation of the king curve along the branch:
`(1 + z + z²)(1 + Y + Y²) = z Y`. -/
lemma K_Yb : (1 + X + X ^ 2) * (1 + Yb + Yb ^ 2) - X * Yb = 0 := by
  set D : PK := C k0 * uu s_z0 * uu s_zr with hD
  set E : PK := uu s_q1 * uu s_q2 with hE
  set Nn : PK := C (om ^ 2) * uu s_b1 * uu s_b2 with hN
  have hXD : X * D = Gb := by rw [Gb_eq', hD, w0]; ring
  have hE0 : constantCoeff E ≠ 0 := by simp [hE, const_uu]
  have hD0 : constantCoeff D ≠ 0 := by simp [hD, const_uu, k0_ne]
  have hYE : Yb * E = Nn := by
    have h1 : constantCoeff (uu s_q1) ≠ 0 := by simp [const_uu]
    have h2 : constantCoeff (uu s_q2) ≠ 0 := by simp [const_uu]
    rw [Yb, hE, hN]
    rw [show C (om ^ 2) * uu s_b1 * uu s_b2 * (uu s_q1)⁻¹ * (uu s_q2)⁻¹ * (uu s_q1 * uu s_q2) =
      C (om ^ 2) * uu s_b1 * uu s_b2 * ((uu s_q1)⁻¹ * uu s_q1) * ((uu s_q2)⁻¹ * uu s_q2) by ring,
      PowerSeries.inv_mul_cancel _ h1, PowerSeries.inv_mul_cancel _ h2]; ring
  have key : ((1 + X + X ^ 2) * (1 + Yb + Yb ^ 2) - X * Yb) * (D ^ 2 * E ^ 2) =
      (D ^ 2 + Gb * D + Gb ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2) - Gb * D * Nn * E := by
    rw [← hXD, ← hYE]; ring
  have hpoly : (D ^ 2 + Gb * D + Gb ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2) - Gb * D * Nn * E = 0 := by
    set Gt : PK := C ((1 : KK) / 6) * Gb with hGt
    have hG6 : Gb = 6 * Gt := by
      rw [hGt, ← mul_assoc, ← map_ofNat C 6, ← map_mul]; norm_num
    have h_z0 : C s_z0 * Gb = ((6 : PK) + (12 : PK) * C om) * Gt := by
      rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show s_z0 * 6 = (6 : KK) + (12 : KK) * om by simp only [s_z0]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have h_zr : C s_zr * Gb = ((-3 : PK) + (-6 : PK) * C om) * Gt := by
      rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show s_zr * 6 = (-3 : KK) + (-6 : KK) * om by simp only [s_zr]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have h_b1 : C s_b1 * Gb = ((-3 : PK) + (3 : PK) * C om) * Gt := by
      rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show s_b1 * 6 = (-3 : KK) + (3 : KK) * om by simp only [s_b1]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have h_b2 : C s_b2 * Gb = ((6 : PK) + (-6 : PK) * C om) * Gt := by
      rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show s_b2 * 6 = (6 : KK) + (-6 : KK) * om by simp only [s_b2]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have h_q1 : C s_q1 * Gb = ((6 : PK) + (3 : PK) * C om) * Gt := by
      rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show s_q1 * 6 = (6 : KK) + (3 : KK) * om by simp only [s_q1]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have h_q2 : C s_q2 * Gb = ((-12 : PK) + (-6 : PK) * C om) * Gt := by
      rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show s_q2 * 6 = (-12 : KK) + (-6 : KK) * om by simp only [s_q2]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have h_k9 : (9 : PK) * C k0 = ((-2 : PK) + (-4 : PK) * C om) := by
      rw [← map_ofNat C 9, ← map_mul, show (9 : KK) * k0 = (-2 : KK) + (-4 : KK) * om by simp only [k0]; ring]
      simp [map_add, map_mul, map_neg, map_ofNat]
    have hom : C om ^ 2 + C om + 1 = (0 : PK) := by rw [← map_pow, ← map_add, ← map_one C, ← map_add, om_rel, map_zero]
    have hpoly9 : ((((-2 : PK) + (-4 : PK) * C om) * (1 - ((6 : PK) + (12 : PK) * C om) * Gt) * (1 - ((-3 : PK) + (-6 : PK) * C om) * Gt)) ^ 2 + (54 * Gt) * (((-2 : PK) + (-4 : PK) * C om) * (1 - ((6 : PK) + (12 : PK) * C om) * Gt) * (1 - ((-3 : PK) + (-6 : PK) * C om) * Gt)) + (54 * Gt) ^ 2) * (((1 - ((6 : PK) + (3 : PK) * C om) * Gt) * (1 - ((-12 : PK) + (-6 : PK) * C om) * Gt)) ^ 2 + (C om ^ 2 * (1 - ((-3 : PK) + (3 : PK) * C om) * Gt) * (1 - ((6 : PK) + (-6 : PK) * C om) * Gt)) * ((1 - ((6 : PK) + (3 : PK) * C om) * Gt) * (1 - ((-12 : PK) + (-6 : PK) * C om) * Gt)) + (C om ^ 2 * (1 - ((-3 : PK) + (3 : PK) * C om) * Gt) * (1 - ((6 : PK) + (-6 : PK) * C om) * Gt)) ^ 2) - (54 * Gt) * (((-2 : PK) + (-4 : PK) * C om) * (1 - ((6 : PK) + (12 : PK) * C om) * Gt) * (1 - ((-3 : PK) + (-6 : PK) * C om) * Gt)) * (C om ^ 2 * (1 - ((-3 : PK) + (3 : PK) * C om) * Gt) * (1 - ((6 : PK) + (-6 : PK) * C om) * Gt)) * ((1 - ((6 : PK) + (3 : PK) * C om) * Gt) * (1 - ((-12 : PK) + (-6 : PK) * C om) * Gt)) = 0 := by
      linear_combination ((26873856 : PK) * Gt ^ 8 * C om ^ 12 + (-53747712 : PK) * Gt ^ 8 * C om ^ 11 + (-6718464 : PK) * Gt ^ 8 * C om ^ 10 + (235146240 : PK) * Gt ^ 8 * C om ^ 9 + (45349632 : PK) * Gt ^ 8 * C om ^ 8 + (-80621568 : PK) * Gt ^ 8 * C om ^ 7 + (1031704128 : PK) * Gt ^ 8 * C om ^ 6 + (2485411776 : PK) * Gt ^ 8 * C om ^ 5 + (2550916800 : PK) * Gt ^ 8 * C om ^ 4 + (1454547456 : PK) * Gt ^ 8 * C om ^ 3 + (482049792 : PK) * Gt ^ 8 * C om ^ 2 + (87340032 : PK) * Gt ^ 8 * C om ^ 1 + (6718464 : PK) * Gt ^ 8 * C om ^ 0 + (-4478976 : PK) * Gt ^ 7 * C om ^ 11 + (-2239488 : PK) * Gt ^ 7 * C om ^ 10 + (20715264 : PK) * Gt ^ 7 * C om ^ 9 + (-34432128 : PK) * Gt ^ 7 * C om ^ 8 + (-36531648 : PK) * Gt ^ 7 * C om ^ 7 + (-14486688 : PK) * Gt ^ 7 * C om ^ 6 + (-56896992 : PK) * Gt ^ 7 * C om ^ 5 + (48288960 : PK) * Gt ^ 7 * C om ^ 4 + (231996960 : PK) * Gt ^ 7 * C om ^ 3 + (214850880 : PK) * Gt ^ 7 * C om ^ 2 + (81181440 : PK) * Gt ^ 7 * C om ^ 1 + (11197440 : PK) * Gt ^ 7 * C om ^ 0 + (-4292352 : PK) * Gt ^ 6 * C om ^ 10 + (3919104 : PK) * Gt ^ 6 * C om ^ 9 + (886464 : PK) * Gt ^ 6 * C om ^ 8 + (-18009216 : PK) * Gt ^ 6 * C om ^ 7 + (-18254160 : PK) * Gt ^ 6 * C om ^ 6 + (-42608592 : PK) * Gt ^ 6 * C om ^ 5 + (-78230448 : PK) * Gt ^ 6 * C om ^ 4 + (-107728704 : PK) * Gt ^ 6 * C om ^ 3 + (-57795120 : PK) * Gt ^ 6 * C om ^ 2 + (1959552 : PK) * Gt ^ 6 * C om ^ 1 + (14043456 : PK) * Gt ^ 6 * C om ^ 0 + (248832 : PK) * Gt ^ 5 * C om ^ 9 + (528768 : PK) * Gt ^ 5 * C om ^ 8 + (-552096 : PK) * Gt ^ 5 * C om ^ 7 + (1527984 : PK) * Gt ^ 5 * C om ^ 6 + (-1699056 : PK) * Gt ^ 5 * C om ^ 5 + (-1444392 : PK) * Gt ^ 5 * C om ^ 4 + (-1557144 : PK) * Gt ^ 5 * C om ^ 3 + (-3186216 : PK) * Gt ^ 5 * C om ^ 2 + (-5824224 : PK) * Gt ^ 5 * C om ^ 1 + (-3631392 : PK) * Gt ^ 5 * C om ^ 0 + (238464 : PK) * Gt ^ 4 * C om ^ 8 + (88128 : PK) * Gt ^ 4 * C om ^ 7 + (230688 : PK) * Gt ^ 4 * C om ^ 6 + (533952 : PK) * Gt ^ 4 * C om ^ 5 + (411804 : PK) * Gt ^ 4 * C om ^ 4 + (1059804 : PK) * Gt ^ 4 * C om ^ 3 + (1009260 : PK) * Gt ^ 4 * C om ^ 2 + (616896 : PK) * Gt ^ 4 * C om ^ 1 + (-173664 : PK) * Gt ^ 4 * C om ^ 0 + (6912 : PK) * Gt ^ 3 * C om ^ 7 + (18144 : PK) * Gt ^ 3 * C om ^ 6 + (43848 : PK) * Gt ^ 3 * C om ^ 5 + (-3996 : PK) * Gt ^ 3 * C om ^ 4 + (42876 : PK) * Gt ^ 3 * C om ^ 3 + (1836 : PK) * Gt ^ 3 * C om ^ 2 + (23328 : PK) * Gt ^ 3 * C om ^ 1 + (50760 : PK) * Gt ^ 3 * C om ^ 0 + (-3312 : PK) * Gt ^ 2 * C om ^ 6 + (-288 : PK) * Gt ^ 2 * C om ^ 5 + (-1116 : PK) * Gt ^ 2 * C om ^ 4 + (-3636 : PK) * Gt ^ 2 * C om ^ 3 + (-1332 : PK) * Gt ^ 2 * C om ^ 2 + (-7956 : PK) * Gt ^ 2 * C om ^ 1 + (1116 : PK) * Gt ^ 2 * C om ^ 0 + (-96 : PK) * Gt ^ 1 * C om ^ 5 + (-192 : PK) * Gt ^ 1 * C om ^ 4 + (-240 : PK) * Gt ^ 1 * C om ^ 3 + (132 : PK) * Gt ^ 1 * C om ^ 2 + (-60 : PK) * Gt ^ 1 * C om ^ 1 + (-84 : PK) * Gt ^ 1 * C om ^ 0 + (16 : PK) * Gt ^ 0 * C om ^ 4 + (4 : PK) * Gt ^ 0 * C om ^ 2 + (12 : PK) * Gt ^ 0 * C om ^ 1 + (4 : PK) * Gt ^ 0 * C om ^ 0) * hom
    have e9D : (9 : PK) * D = ((-2 : PK) + (-4 : PK) * C om) * (1 - ((6 : PK) + (12 : PK) * C om) * Gt) * (1 - ((-3 : PK) + (-6 : PK) * C om) * Gt) := by
      rw [hD, uu, uu, h_z0, h_zr, ← h_k9]; ring
    have e9G : (9 : PK) * Gb = (54 * Gt) := by rw [hG6]; ring
    have eE : E = ((1 - ((6 : PK) + (3 : PK) * C om) * Gt) * (1 - ((-12 : PK) + (-6 : PK) * C om) * Gt)) := by rw [hE, uu, uu, h_q1, h_q2]
    have eN : Nn = (C om ^ 2 * (1 - ((-3 : PK) + (3 : PK) * C om) * Gt) * (1 - ((6 : PK) + (-6 : PK) * C om) * Gt)) := by rw [hN, uu, uu, h_b1, h_b2, map_pow]
    have h81 : ((9 * D) ^ 2 + (9 * Gb) * (9 * D) + (9 * Gb) ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2)
        - (9 * Gb) * (9 * D) * Nn * E = 0 := by
      rw [e9D, e9G, eE, eN]; exact hpoly9
    have h81' : ((D ^ 2 + Gb * D + Gb ^ 2) * (E ^ 2 + Nn * E + Nn ^ 2) - Gb * D * Nn * E) * 81 = 0 := by
      rw [← h81]; ring
    have h810 : constantCoeff (81 : PK) ≠ 0 := by
      rw [show (81 : PK) = C 81 from (map_ofNat C 81).symm, constantCoeff_C]; norm_num
    exact cancel1 h810 (by rw [h81', zero_mul])
  rw [hpoly] at key
  have hu : constantCoeff (D ^ 2 * E ^ 2) ≠ 0 := by
    rw [map_mul, map_pow, map_pow]; exact mul_ne_zero (pow_ne_zero _ hD0) (pow_ne_zero _ hE0)
  exact cancel1 hu (by rw [key, zero_mul])

end A094061
