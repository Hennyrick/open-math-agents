import Mathlib

/-!
Two-variable power series over ℚ: Euler derivatives, p-integrality, logarithm via log-derivatives.
Part of the A094061 formalisation (Claude Code, continuing Hennyrick's research line).
-/

namespace A094061

open MvPowerSeries

abbrev PS := MvPowerSeries (Fin 2) ℚ

/-- `q` is `p`-integral. -/
def pint (p : ℕ) (q : ℚ) : Prop := ¬ p ∣ q.den

lemma pint_add {p : ℕ} (hp : p.Prime) {a b : ℚ} (ha : pint p a) (hb : pint p b) :
    pint p (a + b) := by
  intro h
  have h1 : p ∣ a.den * b.den := dvd_trans h (Rat.add_den_dvd a b)
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact ha h2
  · exact hb h2

lemma pint_mul {p : ℕ} (hp : p.Prime) {a b : ℚ} (ha : pint p a) (hb : pint p b) :
    pint p (a * b) := by
  intro h
  have h1 : p ∣ a.den * b.den := dvd_trans h (Rat.mul_den_dvd a b)
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact ha h2
  · exact hb h2

lemma pint_int {p : ℕ} (hp : p.Prime) (z : ℤ) : pint p (z : ℚ) := by
  intro h; simp at h; exact hp.one_lt.ne' h

lemma pint_nat {p : ℕ} (hp : p.Prime) (z : ℕ) : pint p (z : ℚ) := by
  have := pint_int hp (z : ℤ); simpa using this

lemma pint_neg {p : ℕ} {a : ℚ} (ha : pint p a) : pint p (-a) := by
  simpa [pint] using ha

lemma pint_sub {p : ℕ} (hp : p.Prime) {a b : ℚ} (ha : pint p a) (hb : pint p b) :
    pint p (a - b) := by
  rw [sub_eq_add_neg]; exact pint_add hp ha (pint_neg hb)

lemma pint_zero {p : ℕ} (hp : p.Prime) : pint p 0 := by simpa using pint_int hp 0

lemma pint_sum {p : ℕ} (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, pint p (f i)) : pint p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pint_zero hp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pint_add hp (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Inverse of a natural number prime to `p` is `p`-integral. -/
lemma pint_inv_nat {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : ¬ p ∣ m) : pint p ((m : ℚ)⁻¹) := by
  intro h
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have : ((m : ℚ)⁻¹).den = m := by
    rw [Rat.inv_natCast_den]; simp [hm0]
  rw [this] at h; exact hm h

/-- A rational that is an integer times `p`-integral and divisible by `p^k` gives integer
divisibility. -/
lemma dvd_of_pint {p : ℕ} (hp : p.Prime) (k : ℕ) (z : ℤ) (h : pint p ((z : ℚ) / (p : ℚ) ^ k)) :
    (p : ℤ) ^ k ∣ z := by
  set q : ℚ := (z : ℚ) / (p : ℚ) ^ k with hq
  have hpk : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hz : (z : ℚ) = (p : ℚ) ^ k * q := by rw [hq]; field_simp
  have e : (z : ℚ) * q.den = (p : ℚ) ^ k * q.num := by
    rw [hz, mul_assoc, Rat.mul_den_eq_num]
  have e' : z * q.den = (p : ℤ) ^ k * q.num := by exact_mod_cast e
  have hcop : IsCoprime ((p : ℤ) ^ k) (q.den : ℤ) := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime p q.den := (Nat.Prime.coprime_iff_not_dvd hp).2 h
    simpa [Int.gcd_natCast_natCast] using this
  exact hcop.dvd_of_dvd_mul_right ⟨q.num, by rw [← e']⟩

/-! Euler derivatives. -/

/-- `D i = X_i ∂/∂X_i`. -/
noncomputable def D (i : Fin 2) (F : PS) : PS := X i * pderiv ℚ i F

lemma coeff_D (i : Fin 2) (F : PS) (d : Fin 2 →₀ ℕ) :
    coeff d (D i F) = (d i : ℚ) * coeff d F := by
  classical
  rw [D, X, coeff_monomial_mul, one_mul]
  split_ifs with h
  · rw [coeff_pderiv]
    have hd : d - Finsupp.single i 1 + Finsupp.single i 1 = d := tsub_add_cancel_of_le h
    rw [hd]
    have h1 : 1 ≤ d i := by simpa using (Finsupp.le_def.1 h) i
    have : (((d - Finsupp.single i 1 : Fin 2 →₀ ℕ) i : ℕ) : ℚ) + 1 = d i := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
      rw [Nat.cast_sub h1]; ring
    rw [this, mul_comm]
  · have : d i = 0 := by
      by_contra hne
      apply h
      intro j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Ne.symm hj]
    simp [this]

lemma D_mul (i : Fin 2) (F G : PS) : D i (F * G) = F * D i G + G * D i F := by
  simp only [D, Derivation.leibniz, smul_eq_mul]; ring

lemma D_add (i : Fin 2) (F G : PS) : D i (F + G) = D i F + D i G := by
  simp only [D, map_add]; ring

lemma D_sub (i : Fin 2) (F G : PS) : D i (F - G) = D i F - D i G := by
  simp only [D, map_sub]; ring

lemma D_smul (i : Fin 2) (c : ℚ) (F : PS) : D i (c • F) = c • D i F := by
  simp only [D]; rw [(pderiv ℚ i).map_smul, mul_smul_comm]

lemma D_C (i : Fin 2) (c : ℚ) : D i (C c) = 0 := by
  simp [D]

lemma D_pow (i : Fin 2) (F : PS) (n : ℕ) : D i (F ^ n) = (n : PS) * F ^ (n - 1) * D i F := by
  simp only [D, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]; ring

lemma D_comm (F : PS) : D 0 (D 1 F) = D 1 (D 0 F) := by
  ext d; simp only [coeff_D]; ring

lemma coeff_zero_D (i : Fin 2) (F : PS) : constantCoeff (D i F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_D]; simp

/-- Two series with equal Euler derivatives and equal constant terms are equal. -/
lemma eq_of_D_eq {F G : PS} (h0 : D 0 F = D 0 G) (h1 : D 1 F = D 1 G)
    (hc : constantCoeff F = constantCoeff G) : F = G := by
  ext d
  by_cases hd0 : d 0 = 0
  · by_cases hd1 : d 1 = 0
    · have : d = 0 := by ext j; fin_cases j <;> simp [hd0, hd1]
      subst this
      simpa [coeff_zero_eq_constantCoeff_apply] using hc
    · have := congrArg (coeff d) h1
      rw [coeff_D, coeff_D] at this
      exact mul_left_cancel₀ (by exact_mod_cast hd1) this
  · have := congrArg (coeff d) h0
    rw [coeff_D, coeff_D] at this
    exact mul_left_cancel₀ (by exact_mod_cast hd0) this

lemma D_inv (i : Fin 2) {F : PS} (hF : constantCoeff F ≠ 0) :
    D i F⁻¹ = - (F⁻¹ * F⁻¹) * D i F := by
  have h := congrArg (D i) (MvPowerSeries.mul_inv_cancel F hF)
  rw [D_mul] at h
  have h1 : D i (1 : PS) = 0 := by simpa using D_C i 1
  rw [h1] at h
  have hinv : F⁻¹ * F = 1 := MvPowerSeries.inv_mul_cancel F hF
  calc D i F⁻¹ = (F⁻¹ * F) * D i F⁻¹ := by rw [hinv, one_mul]
    _ = F⁻¹ * (F * D i F⁻¹ + F⁻¹ * D i F) - (F⁻¹ * F⁻¹) * D i F := by ring
    _ = - (F⁻¹ * F⁻¹) * D i F := by rw [h]; ring

/-- Log-derivative `D_i F / F`. -/
noncomputable def ld (i : Fin 2) (F : PS) : PS := D i F * F⁻¹

lemma ld_closed {F : PS} (hF : constantCoeff F ≠ 0) : D 1 (ld 0 F) = D 0 (ld 1 F) := by
  simp only [ld, D_mul, D_inv _ hF, D_comm]; ring

lemma coeff_closed {F : PS} (hF : constantCoeff F ≠ 0) (d : Fin 2 →₀ ℕ) :
    (d 1 : ℚ) * coeff d (ld 0 F) = (d 0 : ℚ) * coeff d (ld 1 F) := by
  have := congrArg (coeff d) (ld_closed hF)
  rwa [coeff_D, coeff_D] at this

lemma const_ld (i : Fin 2) (F : PS) : constantCoeff (ld i F) = 0 := by
  simp [ld, coeff_zero_D]

/-- Logarithm of a series with nonzero constant term, defined through its log-derivatives,
normalised to have constant term zero. -/
noncomputable def logS (F : PS) : PS := fun d =>
  if d 0 ≠ 0 then coeff d (ld 0 F) / d 0
  else if d 1 ≠ 0 then coeff d (ld 1 F) / d 1 else 0

lemma coeff_logS (F : PS) (d : Fin 2 →₀ ℕ) : coeff d (logS F) =
    if d 0 ≠ 0 then coeff d (ld 0 F) / d 0
    else if d 1 ≠ 0 then coeff d (ld 1 F) / d 1 else 0 := rfl

lemma const_logS (F : PS) : constantCoeff (logS F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logS]; simp

lemma D_logS (i : Fin 2) {F : PS} (hF : constantCoeff F ≠ 0) : D i (logS F) = ld i F := by
  ext d
  rw [coeff_D, coeff_logS]
  have hc := coeff_closed hF d
  have h00 : d 0 = 0 → d 1 = 0 → d = 0 := fun a b => by ext j; fin_cases j <;> simp [a, b]
  fin_cases i
  · simp only
    by_cases h0 : d 0 = 0
    · by_cases h1 : d 1 = 0
      · have := h00 h0 h1; subst this
        simp [coeff_zero_eq_constantCoeff_apply, const_ld]
      · simp [h0, h1]
        have : (d 1 : ℚ) ≠ 0 := by exact_mod_cast h1
        have hc' : (d 1 : ℚ) * coeff d (ld 0 F) = 0 := by rw [hc, h0]; simp
        rcases mul_eq_zero.1 hc' with h | h
        · exact absurd h this
        · exact h.symm
    · have : (d 0 : ℚ) ≠ 0 := by exact_mod_cast h0
      simp [h0]; field_simp
  · simp only
    by_cases h0 : d 0 = 0
    · by_cases h1 : d 1 = 0
      · have := h00 h0 h1; subst this
        simp [coeff_zero_eq_constantCoeff_apply, const_ld]
      · have : (d 1 : ℚ) ≠ 0 := by exact_mod_cast h1
        simp [h0, h1]; field_simp
    · have : (d 0 : ℚ) ≠ 0 := by exact_mod_cast h0
      simp [h0]
      field_simp
      linear_combination hc

lemma cancel_right {X Y H : PS} (hH : constantCoeff H ≠ 0) (h : X * H = Y * H) : X = Y := by
  have := congrArg (· * H⁻¹) h
  simp only [mul_assoc, MvPowerSeries.mul_inv_cancel H hH, mul_one] at this
  exact this

lemma ld_mul (i : Fin 2) {F G : PS} (hF : constantCoeff F ≠ 0) (hG : constantCoeff G ≠ 0) :
    ld i (F * G) = ld i F + ld i G := by
  have hFG : constantCoeff (F * G) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hF hG
  apply cancel_right hFG
  simp only [ld, D_mul]
  have e1 : (F * D i G + G * D i F) * (F * G)⁻¹ * (F * G) = F * D i G + G * D i F := by
    rw [mul_assoc, MvPowerSeries.inv_mul_cancel _ hFG, mul_one]
  rw [e1]
  have e2 : (D i F * F⁻¹ + D i G * G⁻¹) * (F * G) =
      D i F * G * (F⁻¹ * F) + D i G * F * (G⁻¹ * G) := by ring
  rw [e2, MvPowerSeries.inv_mul_cancel _ hF, MvPowerSeries.inv_mul_cancel _ hG]; ring

lemma logS_mul {F G : PS} (hF : constantCoeff F ≠ 0) (hG : constantCoeff G ≠ 0) :
    logS (F * G) = logS F + logS G := by
  have hFG : constantCoeff (F * G) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hF hG
  apply eq_of_D_eq
  · rw [D_add, D_logS 0 hFG, D_logS 0 hF, D_logS 0 hG, ld_mul 0 hF hG]
  · rw [D_add, D_logS 1 hFG, D_logS 1 hF, D_logS 1 hG, ld_mul 1 hF hG]
  · simp [const_logS]

lemma D_one (i : Fin 2) : D i (1 : PS) = 0 := by simpa using D_C i 1

lemma logS_one : logS (1 : PS) = 0 := by
  ext d
  rw [coeff_logS]
  simp [ld, D_one]

lemma logS_pow {F : PS} (hF : constantCoeff F ≠ 0) (n : ℕ) : logS (F ^ n) = (n : ℚ) • logS F := by
  induction n with
  | zero => simp [logS_one]
  | succ n ih =>
    have hFn : constantCoeff (F ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hF
    rw [pow_succ, logS_mul hFn hF, ih]; push_cast; rw [add_smul, one_smul]

/-! Frobenius `x ↦ x^p, y ↦ y^p`. -/

noncomputable def Phi (p : ℕ) (hp : p ≠ 0) : PS →ₐ[ℚ] PS := MvPowerSeries.expand p hp

lemma exists_smul_of_dvd {p : ℕ} (d : Fin 2 →₀ ℕ) (h : ∀ j, p ∣ d j) :
    ∃ m : Fin 2 →₀ ℕ, d = p • m := by
  refine ⟨Finsupp.mapRange (fun a => a / p) (by simp) d, ?_⟩
  ext j
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact (Nat.mul_div_cancel' (h j)).symm

lemma D_Phi (i : Fin 2) {p : ℕ} (hp : p ≠ 0) (F : PS) :
    D i (Phi p hp F) = (p : ℚ) • Phi p hp (D i F) := by
  ext d
  rw [coeff_D, coeff_smul]
  by_cases h : ∀ j, p ∣ d j
  · obtain ⟨m, rfl⟩ := exists_smul_of_dvd d h
    simp only [Phi, coeff_expand_smul, coeff_D, Finsupp.smul_apply, smul_eq_mul]
    push_cast; ring
  · push Not at h
    obtain ⟨j, hj⟩ := h
    simp only [Phi, coeff_expand_of_not_dvd p hp _ hj]; ring

lemma const_Phi {p : ℕ} (hp : p ≠ 0) (F : PS) : constantCoeff (Phi p hp F) = constantCoeff F := by
  simp [Phi, constantCoeff_expand]

lemma Phi_inv {p : ℕ} (hp : p ≠ 0) {F : PS} (hF : constantCoeff F ≠ 0) :
    Phi p hp F⁻¹ = (Phi p hp F)⁻¹ := by
  have h1 : constantCoeff (Phi p hp F) ≠ 0 := by rw [const_Phi]; exact hF
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one h1, ← map_mul, MvPowerSeries.inv_mul_cancel _ hF, map_one]

lemma logS_Phi {p : ℕ} (hp : p ≠ 0) {F : PS} (hF : constantCoeff F ≠ 0) :
    logS (Phi p hp F) = Phi p hp (logS F) := by
  have h1 : constantCoeff (Phi p hp F) ≠ 0 := by rw [const_Phi]; exact hF
  apply eq_of_D_eq
  · rw [D_logS 0 h1, D_Phi, D_logS 0 hF, ld, ld, map_mul, D_Phi, Phi_inv hp hF, smul_mul_assoc]
  · rw [D_logS 1 h1, D_Phi, D_logS 1 hF, ld, ld, map_mul, D_Phi, Phi_inv hp hF, smul_mul_assoc]
  · rw [const_logS, const_Phi, const_logS]

/-! Order (vanishing of low-degree coefficients) and the exponential. -/

/-- Total degree of a bidegree. -/
def deg (d : Fin 2 →₀ ℕ) : ℕ := d 0 + d 1

lemma deg_add (a b : Fin 2 →₀ ℕ) : deg (a + b) = deg a + deg b := by
  simp [deg]; ring

lemma eq_zero_of_deg (d : Fin 2 →₀ ℕ) (h : deg d = 0) : d = 0 := by
  simp only [deg] at h
  ext j; fin_cases j <;> simp <;> omega

/-- All coefficients of total degree below `k` vanish. -/
def Van (k : ℕ) (F : PS) : Prop := ∀ d, deg d < k → coeff d F = 0

lemma Van_mul {a b : ℕ} {F G : PS} (hF : Van a F) (hG : Van b G) : Van (a + b) (F * G) := by
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have := deg_add x.1 x.2
  rw [hx] at this
  by_cases h1 : deg x.1 < a
  · rw [hF _ h1, zero_mul]
  · rw [hG _ (by omega), mul_zero]

lemma Van_one_of_const {G : PS} (hG : constantCoeff G = 0) : Van 1 G := by
  intro d hd
  have : d = 0 := eq_zero_of_deg d (by omega)
  subst this; simpa [coeff_zero_eq_constantCoeff_apply] using hG

lemma Van_zero (F : PS) : Van 0 F := fun d hd => absurd hd (Nat.not_lt_zero _)

lemma Van_pow {G : PS} (hG : constantCoeff G = 0) (j : ℕ) : Van j (G ^ j) := by
  induction j with
  | zero => exact Van_zero _
  | succ j ih => rw [pow_succ]; exact Van_mul ih (Van_one_of_const hG)

/-- Exponential of a series with zero constant term, coefficientwise a finite sum. -/
noncomputable def expS (G : PS) : PS := fun d =>
  ∑ j ∈ Finset.range (deg d + 1), coeff d (G ^ j) / (j.factorial : ℚ)

lemma coeff_expS {G : PS} (hG : constantCoeff G = 0) (d : Fin 2 →₀ ℕ) {M : ℕ} (hM : deg d ≤ M) :
    coeff d (expS G) = ∑ j ∈ Finset.range (M + 1), coeff d (G ^ j) / (j.factorial : ℚ) := by
  show (∑ j ∈ Finset.range (deg d + 1), coeff d (G ^ j) / (j.factorial : ℚ)) = _
  apply Finset.sum_subset
  · intro j hj; simp at hj ⊢; omega
  · intro j _ hj
    simp at hj
    rw [Van_pow hG j d (by omega), zero_div]

lemma const_expS (G : PS) : constantCoeff (expS G) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  show (∑ j ∈ Finset.range (deg 0 + 1), coeff 0 (G ^ j) / (j.factorial : ℚ)) = 1
  simp [deg]

lemma D_expS (i : Fin 2) {G : PS} (hG : constantCoeff G = 0) : D i (expS G) = D i G * expS G := by
  ext d
  set N := deg d with hN
  rw [coeff_D, coeff_expS hG d (le_refl N), Finset.mul_sum, coeff_mul]
  -- right side
  have hR : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal d, coeff x.1 (D i G) * coeff x.2 (expS G) =
      ∑ j ∈ Finset.range (N + 1), coeff d (D i G * G ^ j) / (j.factorial : ℚ) := by
    have : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal d, coeff x.1 (D i G) * coeff x.2 (expS G) =
        ∑ j ∈ Finset.range (N + 1), coeff x.1 (D i G) * coeff x.2 (G ^ j) / (j.factorial : ℚ) := by
      intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hle : deg x.2 ≤ N := by rw [hN, ← hx, deg_add]; omega
      rw [coeff_expS hG x.2 hle, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [coeff_mul, Finset.sum_div]
  rw [hR]
  have hDG : constantCoeff (D i G) = 0 := coeff_zero_D i G
  -- last term vanishes
  rw [Finset.sum_range_succ (fun j => coeff d (D i G * G ^ j) / (j.factorial : ℚ))]
  have hlast : coeff d (D i G * G ^ N) = 0 := by
    have := Van_mul (Van_one_of_const hDG) (Van_pow hG N) d (by omega)
    exact this
  rw [hlast, zero_div, add_zero]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have h0 : (d i : ℚ) * coeff d (1 : PS) = 0 := by
    have : coeff d (D i (1 : PS)) = 0 := by rw [D_one]; simp
    rw [coeff_D] at this; exact this
  rw [h0, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hp : D i (G ^ (j + 1)) = ((j + 1 : ℕ) : PS) * G ^ j * D i G := by
    rw [D_pow]; simp
  have hc : (d i : ℚ) * coeff d (G ^ (j + 1)) = ((j + 1 : ℕ) : ℚ) * coeff d (D i G * G ^ j) := by
    rw [← coeff_D, hp, mul_comm ((j + 1 : ℕ) : PS), mul_comm (G ^ j), mul_assoc,
      ← map_natCast (C (σ := Fin 2) (R := ℚ)), coeff_C_mul]
    ring_nf
  rw [mul_div_assoc', hc, Nat.factorial_succ]
  push_cast
  field_simp

lemma logS_expS {G : PS} (hG : constantCoeff G = 0) : logS (expS G) = G := by
  have h1 : constantCoeff (expS G) ≠ 0 := by rw [const_expS]; norm_num
  apply eq_of_D_eq
  · rw [D_logS 0 h1, ld, D_expS 0 hG, mul_assoc, MvPowerSeries.mul_inv_cancel _ h1, mul_one]
  · rw [D_logS 1 h1, ld, D_expS 1 hG, mul_assoc, MvPowerSeries.mul_inv_cancel _ h1, mul_one]
  · rw [const_logS, hG]

/-- A series is determined by its logarithm and its constant term. -/
lemma eq_of_logS_eq {Z W : PS} (hZ : constantCoeff Z ≠ 0) (hW : constantCoeff W ≠ 0)
    (hl : logS Z = logS W) (hc : constantCoeff Z = constantCoeff W) : Z = W := by
  have hDi : ∀ i, D i (Z * W⁻¹) = 0 := by
    intro i
    have e := congrArg (D i) hl
    rw [D_logS i hZ, D_logS i hW, ld, ld] at e
    have eZ : D i Z = D i W * W⁻¹ * Z := by
      have := congrArg (· * Z) e
      simp only [mul_assoc, MvPowerSeries.inv_mul_cancel Z hZ, mul_one] at this
      rw [this]; ring
    rw [D_mul, D_inv i hW, eZ]; ring
  have hQ : Z * W⁻¹ = 1 := by
    have : Z * W⁻¹ = C (constantCoeff (Z * W⁻¹)) := by
      apply eq_of_D_eq
      · rw [hDi 0, D_C]
      · rw [hDi 1, D_C]
      · simp
    rw [this, map_mul, MvPowerSeries.constantCoeff_inv, hc, mul_inv_cancel₀ hW, map_one]
  have := congrArg (· * W) hQ
  simp only [mul_assoc, MvPowerSeries.inv_mul_cancel W hW, mul_one, one_mul] at this
  exact this

end A094061
