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

lemma om_ne : om ≠ 0 := by
  intro h; have := om_rel; rw [h] at this; simp at this

lemma om2_ne : (-1 - om : KK) ≠ 0 := by
  rw [show (-1 - om : KK) = om ^ 2 by rw [om_sq]; ring]; exact pow_ne_zero 2 om_ne

section coreprop
variable {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
include hp hp5

lemma OIs_uu {s : KK} (hs : OI p s) : OIs p (uu s) :=
  OIs_sub hp (OIs_one hp) (OIs_mul hp (OIs_C hp hs) (OIs_Gb hp hp5))

lemma OIs_ld1_uu {s : KK} (hs : OI p s) : OIs p (ld1 (uu s)) :=
  OIs_mul hp (OIs_E1 hp (OIs_uu hp hp5 hs)) (OIs_inv hp (const_uu s) (OIs_uu hp hp5 hs))

/-- Constant times series, divided by the index, when the constant is `p M` times integral. -/
lemma OI_const_term {M n : ℕ} (hn : 1 ≤ n) (hnM : n ∣ M) {x : KK} (hx : OI p x) {F : PK}
    (hF : OIs p F) : OI p (coeff n (C ((p : KK) * M * x) * F) / n) := by
  obtain ⟨k, rfl⟩ := hnM
  have hn0 : (n : KK) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [coeff_C_mul]
  have : (p : KK) * ((n * k : ℕ) : KK) * x * coeff n F / n = (p : KK) * k * x * coeff n F := by
    push_cast; field_simp
  rw [this]
  exact OI_mul hp (OI_mul hp (OI_mul hp (OI_nat hp p) (OI_nat hp k)) hx) (hF n)

variable (h3 : ¬ 3 ∣ p)
include h3

lemma UK_three (M : ℕ) (hM : 1 ≤ M) {a b c ζ : KK} (hζ : sig p h3 ζ = ζ ^ p) (hζ0 : ζ ≠ 0)
    (h : a * b = ζ * c) :
    UK h3 M a + UK h3 M b - UK h3 M c = (p : KK) * M * (UK h3 M a * UK h3 M b) := by
  have e1 := UK_mul h3 M hp hM a b
  have e2 := UK_mul h3 M hp hM ζ c
  rw [h, e2, UK_root h3 M hζ hζ0] at e1
  linear_combination -e1

lemma UK_four (M : ℕ) (hM : 1 ≤ M) {a b c d ζ : KK} (hζ : sig p h3 ζ = ζ ^ p) (hζ0 : ζ ≠ 0)
    (h : a * b = ζ * (c * d)) :
    UK h3 M a + UK h3 M b - UK h3 M c - UK h3 M d =
      (p : KK) * M * (UK h3 M a * UK h3 M b - UK h3 M c * UK h3 M d) := by
  have e1 := UK_mul h3 M hp hM a b
  have e2 := UK_mul h3 M hp hM ζ (c * d)
  have e3 := UK_mul h3 M hp hM c d
  rw [h, e2, UK_root h3 M hζ hζ0, e3] at e1
  linear_combination -e1

omit hp hp5 in
lemma sig_om_root : sig p h3 om = om ^ p := sig_om h3

omit hp hp5 in
lemma sig_om2_root : sig p h3 (-1 - om) = (-1 - om) ^ p := by
  rw [map_sub, map_neg, map_one, sig_om]
  have h := om_pow_rel h3
  have e : (-1 - om) = om ^ 2 := by rw [om_sq]; ring
  rw [e, ← pow_mul, mul_comm, pow_mul]; linear_combination -h

omit hp hp5 in
lemma sig_one_root : sig p h3 (1 : KK) = 1 ^ p := by simp

end coreprop

section coremain
variable {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h3 : ¬ 3 ∣ p)
include hp hp5

/-- Integrality of one tangential pairing at degree `n`, with `U = UK M`. -/
lemma EP_OI {κ : KK} (hκ : OI p κ) (hκi : OI p κ⁻¹) (hκ0 : κ ≠ 0) {u : PK}
    (hu1 : constantCoeff u = 1) (hu : OIs p u) (N : ℕ) {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    OI p (coeff n (Epair hp h3 κ (UK h3 N.factorial κ) u) / n) := by
  have hM1 : 1 ≤ N.factorial := Nat.factorial_pos N
  have hyp := tangHyp_UK (hp := hp) (h3 := h3) (hp5 := hp5) hκ hκi hκ0 N N.factorial hM1
    (fun m hm hmN => Nat.dvd_factorial hm hmN)
  exact tangential (hp := hp) (h3 := h3) (κ := κ) (Uc := UK h3 N.factorial κ) (u := u) hp5 hκ
    (OI_UK (hp := hp) (h3 := h3) hκ hκi hκ0 hM1) hu1 hu N hyp n hn1 hnN

end coremain

section coreThm
variable {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h3 : ¬ 3 ∣ p)
include hp hp5

lemma UU_Yb : UU hp h3 Yb = Ua hp h3 s_b1 + Ua hp h3 s_b2 - Ua hp h3 s_q1 - Ua hp h3 s_q2 := by
  have i1 : constantCoeff (uu s_q1)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero (const_uu_ne _)
  have i2 : constantCoeff (uu s_q2)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero (const_uu_ne _)
  have hb12 : constantCoeff (uu s_b1 * uu s_b2) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (const_uu_ne _) (const_uu_ne _)
  have hb12q : constantCoeff (uu s_b1 * uu s_b2 * (uu s_q1)⁻¹) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hb12 i1
  have hall : constantCoeff (uu s_b1 * uu s_b2 * (uu s_q1)⁻¹ * (uu s_q2)⁻¹) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hb12q i2
  rw [show Yb = C (om ^ 2) * (uu s_b1 * uu s_b2 * (uu s_q1)⁻¹ * (uu s_q2)⁻¹) by rw [Yb]; ring,
    UU_C_mul hp h3 (pow_ne_zero 2 om_ne) hall, UU_mul hp h3 hb12q i2, UU_mul hp h3 hb12 i1,
    UU_mul hp h3 (const_uu_ne _) (const_uu_ne _), UU_inv hp h3 (const_uu_ne _),
    UU_inv hp h3 (const_uu_ne _)]
  simp only [Ua]; ring

set_option maxHeartbeats 2000000 in
/-- **Core proposition.** `U(Y)` has all coefficients `n·(integral)`. -/
theorem core_prop (N : ℕ) : ∀ n, 1 ≤ n → n ≤ N → OI p (coeff n (UU hp h3 Yb) / n) := by
  intro n hn1 hnN
  set M := N.factorial with hM
  have hM1 : 1 ≤ M := Nat.factorial_pos N
  have hnM : n ∣ M := Nat.dvd_factorial hn1 hnN
  set U : KK → KK := UK h3 M with hU
  have eb1 := core_b hp h3 s_b1 cb1 c0b1 crb1 (U cb1) (U c0b1) (U crb1) cb1_eq c0b1_eq crb1_eq
  have eb2 := core_b hp h3 s_b2 cb2 c0b2 crb2 (U cb2) (U c0b2) (U crb2) cb2_eq c0b2_eq crb2_eq
  have eq1 := core_b hp h3 s_q1 cq1 c0q1 crq1 (U cq1) (U c0q1) (U crq1) cq1_eq c0q1_eq crq1_eq
  have eq2 := core_b hp h3 s_q2 cq2 c0q2 crq2 (U cq2) (U c0q2) (U crq2) cq2_eq c0q2_eq crq2_eq
  -- constant cancellations
  have t1 := UK_three hp hp5 h3 M hM1 (sig_om_root h3) om_ne root_b1
  have t2 := UK_three hp hp5 h3 M hM1 (sig_om2_root h3) om2_ne root_b2
  have t3 := UK_three hp hp5 h3 M hM1 (sig_om2_root h3) om2_ne root_q1
  have t4 := UK_three hp hp5 h3 M hM1 (sig_om_root h3) om_ne root_q2
  have t0 := UK_four hp hp5 h3 M hM1 (sig_one_root h3) one_ne_zero root_0
  have tr := UK_four hp hp5 h3 M hM1 (sig_om2_root h3) om2_ne root_r
  set EP := (Epair hp h3 c0b1 (U c0b1) (uu s_zr) + Epair hp h3 crb1 (U crb1) (uu s_z0)
      - Epair hp h3 cb1 (U cb1) w0) + (Epair hp h3 c0b2 (U c0b2) (uu s_zr)
      + Epair hp h3 crb2 (U crb2) (uu s_z0) - Epair hp h3 cb2 (U cb2) w0)
      - (Epair hp h3 c0q1 (U c0q1) (uu s_zr) + Epair hp h3 crq1 (U crq1) (uu s_z0)
      - Epair hp h3 cq1 (U cq1) w0) - (Epair hp h3 c0q2 (U c0q2) (uu s_zr)
      + Epair hp h3 crq2 (U crq2) (uu s_z0) - Epair hp h3 cq2 (U cq2) w0) with hEP
  set PM : KK := (p : KK) * M
  have hid : UU hp h3 Yb = C (PM * (U c0b1 * U crb1)) * la s_b1 + C (PM * (U c0b2 * U crb2)) * la s_b2
      - C (PM * (U c0q1 * U crq1)) * la s_q1 - C (PM * (U c0q2 * U crq2)) * la s_q2
      - C (PM * (U c0b1 * U c0b2 - U c0q1 * U c0q2)) * la s_z0
      - C (PM * (U crb1 * U crb2 - U crq1 * U crq2)) * la s_zr - EP := by
    rw [UU_Yb hp hp5 h3, hEP, ← t1, ← t2, ← t3, ← t4, ← t0, ← tr]
    simp only [map_add, map_sub]
    linear_combination eb1 + eb2 - eq1 - eq2
  rw [hid]
  have hla : ∀ s, OI p s → OIs p (la s) := fun s hs => OIs_ld1_uu hp hp5 hs
  have hUI : ∀ κ, OI p κ → OI p κ⁻¹ → κ ≠ 0 → OI p (U κ) := fun κ a b c =>
    OI_UK (hp := hp) (h3 := h3) a b c hM1
  have ct : ∀ x s, OI p x → OI p s → OI p (coeff n (C (PM * x) * la s) / n) := by
    intro x s hx hs
    have := OI_const_term hp hp5 (M := M) hn1 hnM hx (hla s hs)
    simpa [PM, mul_assoc] using this
  have hw1 : constantCoeff w0 = 1 := const_w0
  have hwI : OIs p w0 := OIs_mul hp (OIs_uu hp hp5 (OI_s_z0 hp hp5)) (OIs_uu hp hp5 (OI_s_zr hp hp5))
  have hu0 : OIs p (uu s_z0) := OIs_uu hp hp5 (OI_s_z0 hp hp5)
  have hur : OIs p (uu s_zr) := OIs_uu hp hp5 (OI_s_zr hp hp5)
  have ep : ∀ κ u, OI p κ → OI p κ⁻¹ → κ ≠ 0 → constantCoeff u = 1 → OIs p u →
      OI p (coeff n (Epair hp h3 κ (U κ) u) / n) := fun κ u a b c d e =>
    EP_OI hp hp5 h3 a b c d e N hn1 hnN
  have cb1t := ct _ _ (OI_mul hp (hUI _ (OI_c0b1 hp hp5) (OI_c0b1_inv hp hp5) c0b1_ne)
    (hUI _ (OI_crb1 hp hp5) (OI_crb1_inv hp hp5) crb1_ne)) (OI_s_b1 hp hp5)
  have cb2t := ct _ _ (OI_mul hp (hUI _ (OI_c0b2 hp hp5) (OI_c0b2_inv hp hp5) c0b2_ne)
    (hUI _ (OI_crb2 hp hp5) (OI_crb2_inv hp hp5) crb2_ne)) (OI_s_b2 hp hp5)
  have cq1t := ct _ _ (OI_mul hp (hUI _ (OI_c0q1 hp hp5) (OI_c0q1_inv hp hp5) c0q1_ne)
    (hUI _ (OI_crq1 hp hp5) (OI_crq1_inv hp hp5) crq1_ne)) (OI_s_q1 hp hp5)
  have cq2t := ct _ _ (OI_mul hp (hUI _ (OI_c0q2 hp hp5) (OI_c0q2_inv hp hp5) c0q2_ne)
    (hUI _ (OI_crq2 hp hp5) (OI_crq2_inv hp hp5) crq2_ne)) (OI_s_q2 hp hp5)
  have c0t := ct _ _ (OI_sub hp (OI_mul hp (hUI _ (OI_c0b1 hp hp5) (OI_c0b1_inv hp hp5) c0b1_ne)
    (hUI _ (OI_c0b2 hp hp5) (OI_c0b2_inv hp hp5) c0b2_ne))
    (OI_mul hp (hUI _ (OI_c0q1 hp hp5) (OI_c0q1_inv hp hp5) c0q1_ne)
    (hUI _ (OI_c0q2 hp hp5) (OI_c0q2_inv hp hp5) c0q2_ne))) (OI_s_z0 hp hp5)
  have crt := ct _ _ (OI_sub hp (OI_mul hp (hUI _ (OI_crb1 hp hp5) (OI_crb1_inv hp hp5) crb1_ne)
    (hUI _ (OI_crb2 hp hp5) (OI_crb2_inv hp hp5) crb2_ne))
    (OI_mul hp (hUI _ (OI_crq1 hp hp5) (OI_crq1_inv hp hp5) crq1_ne)
    (hUI _ (OI_crq2 hp hp5) (OI_crq2_inv hp hp5) crq2_ne))) (OI_s_zr hp hp5)
  have e1 := ep _ _ (OI_c0b1 hp hp5) (OI_c0b1_inv hp hp5) c0b1_ne (const_uu _) hur
  have e2 := ep _ _ (OI_crb1 hp hp5) (OI_crb1_inv hp hp5) crb1_ne (const_uu _) hu0
  have e3 := ep _ _ (OI_cb1 hp hp5) (OI_cb1_inv hp hp5) cb1_ne hw1 hwI
  have e4 := ep _ _ (OI_c0b2 hp hp5) (OI_c0b2_inv hp hp5) c0b2_ne (const_uu _) hur
  have e5 := ep _ _ (OI_crb2 hp hp5) (OI_crb2_inv hp hp5) crb2_ne (const_uu _) hu0
  have e6 := ep _ _ (OI_cb2 hp hp5) (OI_cb2_inv hp hp5) cb2_ne hw1 hwI
  have e7 := ep _ _ (OI_c0q1 hp hp5) (OI_c0q1_inv hp hp5) c0q1_ne (const_uu _) hur
  have e8 := ep _ _ (OI_crq1 hp hp5) (OI_crq1_inv hp hp5) crq1_ne (const_uu _) hu0
  have e9 := ep _ _ (OI_cq1 hp hp5) (OI_cq1_inv hp hp5) cq1_ne hw1 hwI
  have e10 := ep _ _ (OI_c0q2 hp hp5) (OI_c0q2_inv hp hp5) c0q2_ne (const_uu _) hur
  have e11 := ep _ _ (OI_crq2 hp hp5) (OI_crq2_inv hp hp5) crq2_ne (const_uu _) hu0
  have e12 := ep _ _ (OI_cq2 hp hp5) (OI_cq2_inv hp hp5) cq2_ne hw1 hwI
  have A : ∀ F G : PK, OI p (coeff n F / n) → OI p (coeff n G / n) → OI p (coeff n (F + G) / n) :=
    fun F G hF hG => by rw [map_add, add_div]; exact OI_add hp hF hG
  have B : ∀ F G : PK, OI p (coeff n F / n) → OI p (coeff n G / n) → OI p (coeff n (F - G) / n) :=
    fun F G hF hG => by rw [map_sub, sub_div]; exact OI_sub hp hF hG
  rw [hEP]
  exact B _ _ (B _ _ (B _ _ (B _ _ (B _ _ (A _ _ cb1t cb2t) cq1t) cq2t) c0t) crt)
    (B _ _ (B _ _ (A _ _ (B _ _ (A _ _ e1 e2) e3) (B _ _ (A _ _ e4 e5) e6))
      (B _ _ (A _ _ e7 e8) e9)) (B _ _ (A _ _ e10 e11) e12))

end coreThm

end A094061
