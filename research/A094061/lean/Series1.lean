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


/-! Integrality of one-variable series. -/

/-- All coefficients integral. -/
def OIs (p : ℕ) (f : PK) : Prop := ∀ n, OI p (coeff n f)

/-- Generic binomial identity for a prime exponent. -/
lemma add_pow_prime_sub {R : Type*} [CommRing R] (q : ℕ) (hp : (q + 1).Prime) (A B : R) :
    (A + B) ^ (q + 1) - A ^ (q + 1) - B ^ (q + 1) = ((q + 1 : ℕ) : R) *
      ∑ k ∈ Finset.range q, A ^ (k + 1) * B ^ (q + 1 - (k + 1)) *
        (((q + 1).choose (k + 1) / (q + 1) : ℕ) : R) := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, Nat.choose_zero_right,
    one_mul, Nat.sub_zero]
  rw [Finset.mul_sum]
  have e : ∀ k ∈ Finset.range q, A ^ (k + 1) * B ^ (q + 1 - (k + 1)) * ((q + 1).choose (k + 1) : R)
      = ((q + 1 : ℕ) : R) * (A ^ (k + 1) * B ^ (q + 1 - (k + 1)) *
        (((q + 1).choose (k + 1) / (q + 1) : ℕ) : R)) := by
    intro k hk
    obtain ⟨t, ht⟩ : (q + 1) ∣ (q + 1).choose (k + 1) :=
      hp.dvd_choose_self (by omega) (by simp at hk; omega)
    rw [ht, Nat.mul_div_cancel_left t (Nat.succ_pos q)]; push_cast; ring
  rw [Finset.sum_congr rfl e]; ring

section integ
variable {p : ℕ} (hp : p.Prime)
include hp

lemma OIs_add {f g : PK} (hf : OIs p f) (hg : OIs p g) : OIs p (f + g) := fun n => by
  rw [map_add]; exact OI_add hp (hf n) (hg n)

lemma OIs_sub {f g : PK} (hf : OIs p f) (hg : OIs p g) : OIs p (f - g) := fun n => by
  rw [map_sub]; exact OI_sub hp (hf n) (hg n)

lemma OIs_neg {f : PK} (hf : OIs p f) : OIs p (-f) := fun n => by
  rw [map_neg]; exact OI_neg hp (hf n)

lemma OIs_mul {f g : PK} (hf : OIs p f) (hg : OIs p g) : OIs p (f * g) := fun n => by
  rw [coeff_mul]; exact OI_sum hp _ _ (fun x _ => OI_mul hp (hf _) (hg _))

lemma OIs_C {c : KK} (hc : OI p c) : OIs p (C c) := fun n => by
  rw [coeff_C]; split_ifs
  · exact hc
  · exact OI_zero hp

lemma OIs_one : OIs p (1 : PK) := by simpa using OIs_C hp (OI_one hp)

lemma OIs_X : OIs p (X : PK) := fun n => by
  rw [coeff_X]; split_ifs
  · exact OI_one hp
  · exact OI_zero hp

lemma OIs_pow {f : PK} (hf : OIs p f) (k : ℕ) : OIs p (f ^ k) := by
  induction k with
  | zero => simpa using OIs_one hp
  | succ k ih => rw [pow_succ]; exact OIs_mul hp ih hf

lemma OIs_smul {c : KK} (hc : OI p c) {f : PK} (hf : OIs p f) : OIs p (c • f) := fun n => by
  rw [coeff_smul, smul_eq_mul]; exact OI_mul hp hc (hf n)

lemma OIs_nat (k : ℕ) : OIs p (k : PK) := by
  rw [show (k : PK) = C (k : KK) by simp]; exact OIs_C hp (OI_nat hp k)

lemma OIs_E1 {f : PK} (hf : OIs p f) : OIs p (E1 f) := fun n => by
  rw [coeff_E1]; exact OI_mul hp (OI_nat hp n) (hf n)

lemma OIs_sum {ι : Type*} (s : Finset ι) (f : ι → PK) (h : ∀ i ∈ s, OIs p (f i)) :
    OIs p (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]; exact OI_sum hp _ _ (fun i hi => h i hi n)

lemma OIs_subst {A g : PK} (hA : OIs p A) (hg0 : constantCoeff g = 0) (hg : OIs p g) :
    OIs p (A.subst g) := fun n => by
  rw [coeff_subst_range A hg0]
  exact OI_sum hp _ _ (fun d _ => OI_mul hp (hA d) (OIs_pow hp hg d n))

lemma OIs_inv {f : PK} (hf1 : constantCoeff f = 1) (hf : OIs p f) : OIs p f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv, hf1, inv_one]
    split_ifs
    · exact OI_one hp
    · refine OI_mul hp (OI_neg hp (OI_one hp)) (OI_sum hp _ _ (fun x _ => ?_))
      split_ifs with h
      · exact OI_mul hp (hf _) (ih _ h)
      · exact OI_zero hp

lemma OIs_phi1 (h3 : ¬ 3 ∣ p) {f : PK} (hf : OIs p f) : OIs p (phi1 p hp.ne_zero h3 f) := fun n => by
  rw [coeff_phi1]; split_ifs
  · exact OI_sig hp h3 (hf _)
  · exact OI_zero hp

end integ

/-- `p^(d-1)/d` is `p`-integral. -/
lemma pint_ppow_div {p : ℕ} (hp : p.Prime) {d : ℕ} (hd : 1 ≤ d) :
    pint p ((p : ℚ) ^ (d - 1) / d) := by
  have hfac : d = p ^ (d.factorization p) * ordCompl[p] d := (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  have hu : ¬ p ∣ ordCompl[p] d := Nat.not_dvd_ordCompl hp (by omega)
  set v := d.factorization p
  set u := ordCompl[p] d
  have hv : v ≤ d - 1 := by
    have h1 : p ^ v ≤ d := Nat.ordProj_le p (by omega)
    have h2 : v < p ^ v := Nat.lt_pow_self hp.one_lt
    omega
  have hu0 : (u : ℚ) ≠ 0 := by
    have : u ≠ 0 := by rintro h; rw [h] at hu; exact hu (dvd_zero p)
    exact_mod_cast this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : ℚ) ^ (d - 1) / d = ((p ^ (d - 1 - v) : ℕ) : ℚ) * (u : ℚ)⁻¹ := by
    rw [show (d : ℚ) = (p : ℚ) ^ v * u by exact_mod_cast hfac]
    push_cast
    have : (p : ℚ) ^ (d - 1) = (p : ℚ) ^ (d - 1 - v) * (p : ℚ) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hv]
    rw [this]; field_simp
  rw [e]; exact pint_mul hp (pint_nat hp _) (pint_inv_nat hp hu)

section frobS
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p)
include hp

lemma phi1_X : phi1 p hp.ne_zero h3 X = X ^ p := by simp [phi1]

lemma phi1_C (c : KK) : phi1 p hp.ne_zero h3 (C c) = C (sig p h3 c) := by
  simp [phi1, PowerSeries.expand_C]

lemma pKK_ne : (p : KK) ≠ 0 := by
  have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simpa [rr] using (map_ne_zero (algebraMap ℚ KK)).2 this

/-- Frobenius congruence for series: `f^p ≡ φ(f) mod p`. -/
lemma frob_series : ∀ n, ∀ f : PK, OIs p f →
    OI p (coeff n ((p : KK)⁻¹ • (f ^ p - phi1 p hp.ne_zero h3 f))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  set c := constantCoeff f
  set g : PK := mk fun k => coeff (k + 1) f
  have hfg : f = X * g + C c := eq_X_mul_shift_add_const f
  have hg : OIs p g := fun k => by simp only [g, coeff_mk]; exact hf (k + 1)
  have hc : OI p c := by simpa [c, coeff_zero_eq_constantCoeff_apply] using hf 0
  have hqp : (q + 1).Prime := hq ▸ hp
  set S := ∑ k ∈ Finset.range q, (X * g) ^ (k + 1) * (C c) ^ (q + 1 - (k + 1)) *
    (((q + 1).choose (k + 1) / (q + 1) : ℕ) : PK)
  have hb := add_pow_prime_sub q hqp (X * g) (C c)
  have hS : OIs p S := OIs_sum hp _ _ (fun k _ => OIs_mul hp (OIs_mul hp
    (OIs_pow hp (OIs_mul hp (OIs_X hp) hg) _) (OIs_pow hp (OIs_C hp hc) _)) (OIs_nat hp _))
  have hpK := pKK_ne hp
  have key : (p : KK)⁻¹ • (f ^ p - phi1 p hp.ne_zero h3 f) =
      S + C ((c ^ p - sig p h3 c) / p) + X ^ p * ((p : KK)⁻¹ • (g ^ p - phi1 p hp.ne_zero h3 g)) := by
    have hphi : phi1 p hp.ne_zero h3 f = X ^ p * phi1 p hp.ne_zero h3 g + C (sig p h3 c) := by
      rw [hfg, map_add, map_mul, phi1_X hp h3, phi1_C hp h3]
    rw [hphi]
    conv_lhs => rw [hfg]
    have hb' : (X * g + C c) ^ p = (X * g) ^ p + (C c) ^ p + (p : PK) * S := by
      rw [hq]; rw [← hb]; ring
    rw [hb', mul_pow, ← map_pow]
    rw [show ((p : PK)) = C (p : KK) by simp]
    simp only [smul_sub, smul_add, mul_smul_comm]
    rw [show (p : KK)⁻¹ • (C (p : KK) * S) = S by
      rw [smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hpK, map_one, one_mul]]
    rw [show C ((c ^ p - sig p h3 c) / p) = (p : KK)⁻¹ • (C (c ^ p) - C (sig p h3 c)) by
      rw [smul_eq_C_mul, ← map_sub, ← map_mul]; congr 1; field_simp]
    simp only [smul_sub, smul_eq_C_mul]
    ring
  rw [key, map_add, map_add]
  refine OI_add hp (OI_add hp (hS n) ?_) ?_
  · rw [coeff_C]; split_ifs
    · have := OI_neg hp (frob_cong hp h3 hc)
      rw [show -((sig p h3 c - c ^ p) / p) = (c ^ p - sig p h3 c) / p by ring] at this
      exact this
    · exact OI_zero hp
  · rw [coeff_X_pow_mul']
    split_ifs with hle
    · exact ih (n - p) (by have := hp.one_lt; omega) g hg
    · exact OI_zero hp

end frobS

/-! The logarithm series and Dwork-type integrality of `U`. -/

/-- `log(1 + X) = ∑ (-1)^(k+1) X^k / k`. -/
noncomputable def Lser : PK := mk fun k => if k = 0 then 0 else (-1 : KK) ^ (k + 1) / k

lemma Lser_deriv_mul : d⁄dX KK Lser * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add]
  rcases n with _ | n
  · rw [coeff_zero_mul_X, coeff_derivative]; simp [Lser, coeff_one]
  · rw [coeff_succ_mul_X, coeff_derivative, coeff_derivative]
    simp only [Lser, coeff_mk, coeff_one]
    simp only [Nat.succ_ne_zero, if_false, add_eq_zero, one_ne_zero, and_false]
    have h1 : ((n + 1 : ℕ) : KK) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h2 : ((n + 1 + 1 : ℕ) : KK) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    push_cast at h1 h2 ⊢
    field_simp
    ring

lemma lg_one_add {y : PK} (hy : constantCoeff y = 0) : lg (1 + y) = Lser.subst y := by
  have hs : HasSubst y := HasSubst.of_constantCoeff_zero' hy
  have h1y : constantCoeff (1 + y) ≠ 0 := by simp [hy]
  have e1 : (1 : PK).subst y = 1 := by
    rw [show (1 : PK) = C 1 from (map_one C).symm, subst_C]; exact map_one _
  have hinv : (d⁄dX KK Lser).subst y = (1 + y)⁻¹ := by
    have := congrArg (PowerSeries.subst y) Lser_deriv_mul
    rw [subst_mul hs, subst_add hs, subst_X hs, e1] at this
    rw [PowerSeries.eq_inv_iff_mul_eq_one h1y]
    exact this
  apply eq_of_E1_eq
  · rw [E1_lg, ld1, E1, E1, derivative_subst hs, hinv, map_add, derivative_one, zero_add]
    ring
  · rw [const_lg, ← coeff_zero_eq_constantCoeff_apply, coeff_subst_range _ hy]
    simp [Lser]

section dwork
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p)
include hp

/-- `U(u) = log u - p⁻¹ φ(log u)`. -/
noncomputable def UU (u : PK) : PK := lg u - (p : KK)⁻¹ • phi1 p hp.ne_zero h3 (lg u)

lemma const_UU (u : PK) : constantCoeff (UU hp h3 u) = 0 := by
  simp [UU, const_lg, const_phi1]

lemma OIs_UU {u : PK} (hu1 : constantCoeff u = 1) (hu : OIs p u) : OIs p (UU hp h3 u) := by
  have hpK := pKK_ne hp
  set φu := phi1 p hp.ne_zero h3 u with hφu
  have hφ1 : constantCoeff φu = 1 := by rw [hφu, const_phi1, hu1, map_one]
  have hφi : OIs p φu⁻¹ := OIs_inv hp hφ1 (OIs_phi1 hp h3 hu)
  set w := ((p : KK)⁻¹ • (u ^ p - φu)) * φu⁻¹ with hw
  have hwi : OIs p w := OIs_mul hp (fun n => frob_series hp h3 n u hu) hφi
  have hw0 : constantCoeff w = 0 := by
    rw [hw, map_mul, smul_eq_C_mul, map_mul, map_sub, map_pow, hu1, hφ1]; simp
  have hu0 : constantCoeff u ≠ 0 := by rw [hu1]; exact one_ne_zero
  have hφ0 : constantCoeff φu ≠ 0 := by rw [hφ1]; exact one_ne_zero
  have e1 : u ^ p * φu⁻¹ = 1 + (p : KK) • w := by
    rw [hw, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hpK, one_smul, sub_mul,
      PowerSeries.mul_inv_cancel _ hφ0]; ring
  have e2 : UU hp h3 u = (p : KK)⁻¹ • lg (1 + (p : KK) • w) := by
    rw [← e1, lg_mul (by rw [map_pow]; exact pow_ne_zero _ hu0)
      (by rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hφ0),
      lg_inv hφ0, lg_pow hu0, hφu, lg_phi1 p hp.ne_zero h3 hu0, UU, smul_add, smul_smul,
      inv_mul_cancel₀ hpK, one_smul, smul_neg, sub_eq_add_neg]
  have hy0 : constantCoeff ((p : KK) • w) = 0 := by rw [smul_eq_C_mul, map_mul, hw0, mul_zero]
  rw [e2, lg_one_add hy0]
  intro n
  rw [coeff_smul, coeff_subst_range _ hy0, smul_eq_mul, Finset.mul_sum]
  apply OI_sum hp
  intro d _
  rw [smul_pow, coeff_smul, smul_eq_mul, Lser, coeff_mk]
  split_ifs with hd
  · simp
    exact OI_zero hp
  · have : (p : KK)⁻¹ * ((-1 : KK) ^ (d + 1) / d * ((p : KK) ^ d * coeff n (w ^ d))) =
        rr ((-1) ^ (d + 1) * ((p : ℚ) ^ (d - 1) / d)) * coeff n (w ^ d) := by
      simp only [rr, map_mul, map_pow, map_neg, map_one, map_div₀, map_natCast]
      have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd
      have : (p : KK) ^ d = (p : KK) ^ (d - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hd1]
      rw [this]
      have hdK : (d : KK) ≠ 0 := by exact_mod_cast hd
      field_simp
    rw [this]
    refine OI_mul hp (OI_rat hp (pint_mul hp ?_ (pint_ppow_div hp (Nat.one_le_iff_ne_zero.2 hd))))
      (OIs_pow hp hwi d n)
    simpa using pint_int hp ((-1) ^ (d + 1))

end dwork

end A094061
