import A094061Dev.Series2

/-!
Section 4 of the A094061 argument: from KEY to the supercongruence for diagonal coefficients.
-/

namespace A094061

open MvPowerSeries

/-- All coefficients `p`-integral. -/
def PInt (p : ℕ) (F : PS) : Prop := ∀ d, pint p (coeff d F)

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma PInt_add {F G : PS} (hF : PInt p F) (hG : PInt p G) : PInt p (F + G) := fun d => by
  rw [map_add]; exact pint_add hp (hF d) (hG d)

lemma PInt_sub {F G : PS} (hF : PInt p F) (hG : PInt p G) : PInt p (F - G) := fun d => by
  rw [map_sub]; exact pint_sub hp (hF d) (hG d)

lemma PInt_mul {F G : PS} (hF : PInt p F) (hG : PInt p G) : PInt p (F * G) := fun d => by
  rw [coeff_mul]
  exact pint_sum hp _ _ (fun x _ => pint_mul hp (hF _) (hG _))

lemma PInt_one : PInt p (1 : PS) := fun d => by
  rw [coeff_one]; split_ifs
  · simpa using pint_nat hp 1
  · exact pint_zero hp

lemma PInt_pow {F : PS} (hF : PInt p F) (k : ℕ) : PInt p (F ^ k) := by
  induction k with
  | zero => simpa using PInt_one hp
  | succ k ih => rw [pow_succ]; exact PInt_mul hp ih hF

lemma PInt_D (i : Fin 2) {F : PS} (hF : PInt p F) : PInt p (D i F) := fun d => by
  rw [coeff_D]; exact pint_mul hp (pint_nat hp _) (hF d)

lemma PInt_nsmul {F : PS} (hF : PInt p F) (k : ℕ) : PInt p ((k : ℚ) • F) := fun d => by
  rw [coeff_smul]; exact pint_mul hp (pint_nat hp _) (hF d)

lemma PInt_Phi {F : PS} (hF : PInt p F) : PInt p (Phi p hp.ne_zero F) := fun d => by
  by_cases h : ∀ j, p ∣ d j
  · obtain ⟨m, rfl⟩ := exists_smul_of_dvd d h
    simp only [Phi, coeff_expand_smul]; exact hF m
  · push Not at h
    obtain ⟨j, hj⟩ := h
    simp only [Phi, coeff_expand_of_not_dvd p hp.ne_zero _ hj]; exact pint_zero hp

/-- `N^k / k! / p^(2r)` is `p`-integral when `p^r ∣ N`, `k ≥ 2`, `p ≥ 5`. -/
lemma pint_pow_div_factorial (hp5 : 5 ≤ p) (n r k : ℕ) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    pint p (((n * p ^ r : ℕ) : ℚ) ^ k / (k.factorial : ℚ) / (p : ℚ) ^ (2 * r)) := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p k.factorial with hv
  have hlt : (p - 1) * v < k := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have h4 : 4 * v < k := by
    have : 4 * v ≤ (p - 1) * v := Nat.mul_le_mul_right v (by omega)
    omega
  have hexp : v + 2 * r ≤ r * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hj : j ≤ r * j := Nat.le_mul_of_pos_left j (by omega)
    have hv : v ≤ j := by omega
    nlinarith
  -- factor k! = p^v * u
  have hfac : k.factorial = p ^ v * ordCompl[p] k.factorial := by
    rw [hv, ← Nat.factorization_def _ hp]
    exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
  have hu : ¬ p ∣ ordCompl[p] k.factorial := Nat.not_dvd_ordCompl hp (Nat.factorial_ne_zero k)
  set u := ordCompl[p] k.factorial
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hu0 : (u : ℚ) ≠ 0 := by
    have : u ≠ 0 := by rintro h; rw [h] at hu; exact hu (dvd_zero p)
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t, r * k = t + v + 2 * r := ⟨r * k - v - 2 * r, by omega⟩
  have key : ((n * p ^ r : ℕ) : ℚ) ^ k / (k.factorial : ℚ) / (p : ℚ) ^ (2 * r) =
      ((n ^ k * p ^ t : ℕ) : ℚ) * (u : ℚ)⁻¹ := by
    rw [hfac]
    push_cast
    have e2 : ((p : ℚ) ^ r) ^ k = (p : ℚ) ^ t * (p : ℚ) ^ v * (p : ℚ) ^ (2 * r) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ht]
    rw [mul_pow, e2]
    field_simp
  rw [key]
  exact pint_mul hp (pint_nat hp _) (pint_inv_nat hp hu)

end

/-- Bidegree `(k, k)`. -/
noncomputable def bideg (k : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 k

/-- `L_F = log F - p⁻¹ Φ(log F)`. -/
noncomputable def Lser (p : ℕ) (hp0 : p ≠ 0) (F : PS) : PS :=
  logS F - (p : ℚ)⁻¹ • Phi p hp0 (logS F)

lemma bideg_apply (k : ℕ) (i : Fin 2) : bideg k i = k := by
  fin_cases i <;> simp [bideg]

lemma bideg_mul (p m : ℕ) : bideg (p * m) = p • bideg m := by
  ext i; fin_cases i <;> simp [bideg]

lemma const_smul (c : ℚ) (F : PS) : constantCoeff (c • F) = c * constantCoeff F := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_smul]

section main
variable {p : ℕ} (hp : p.Prime)
include hp

/-- `C * D_i X` has diagonal coefficient divisible by `N` when `D_i C` is `N` times integral. -/
lemma coeff_mul_D_diag (i : Fin 2) (N : ℕ) (C X Y : PS) (hC : PInt p C) (hX : PInt p X)
    (hY : PInt p Y) (hDC : D i C = (N : ℚ) • Y) :
    ∃ q : ℚ, pint p q ∧ coeff (bideg N) (C * D i X) = (N : ℚ) * q := by
  have e : C * D i X = D i (C * X) - X * D i C := by rw [D_mul]; ring
  refine ⟨coeff (bideg N) (C * X) - coeff (bideg N) (X * Y), ?_, ?_⟩
  · exact pint_sub hp (PInt_mul hp hC hX _) (PInt_mul hp hX hY _)
  · rw [e, map_sub, coeff_D, bideg_apply, hDC, mul_smul_comm, coeff_smul]; ring

theorem sec4 (hp5 : 5 ≤ p) (F : PS) (hF1 : constantCoeff F = 1) (hFi : PInt p F)
    (A B : PS) (hA : PInt p A) (hB : PInt p B) (hKEY : Lser p hp.ne_zero F = D 0 A + D 1 B)
    (n r : ℕ) (hr : 1 ≤ r) :
    pint p ((coeff (bideg (n * p ^ r)) (F ^ (n * p ^ r)) -
      coeff (bideg (n * p ^ (r - 1))) (F ^ (n * p ^ (r - 1)))) / (p : ℚ) ^ (2 * r)) := by
  have hp0 := hp.ne_zero
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  set m := n * p ^ (r - 1) with hm
  set N := n * p ^ r with hN
  have hNm : N = p * m := by
    rw [hN, hm]; obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp [pow_succ]; ring
  set l := Lser p hp0 F with hl
  have hF0 : constantCoeff F ≠ 0 := by rw [hF1]; norm_num
  have hl0 : constantCoeff l = 0 := by
    rw [hl, Lser, map_sub, const_smul, const_Phi, const_logS]; simp
  have hli : PInt p l := by
    rw [hKEY]; exact PInt_add hp (PInt_D hp 0 hA) (PInt_D hp 1 hB)
  have hPF : constantCoeff (Phi p hp0 F) ≠ 0 := by rw [const_Phi]; exact hF0
  set C := (Phi p hp0 F) ^ m with hC
  have hCi : PInt p C := PInt_pow hp (PInt_Phi hp hFi) m
  have hC0 : constantCoeff C ≠ 0 := by rw [hC, map_pow]; exact pow_ne_zero _ hPF
  have hNl0 : constantCoeff ((N : ℚ) • l) = 0 := by rw [const_smul, hl0, mul_zero]
  have hE0 : constantCoeff (expS ((N : ℚ) • l)) ≠ 0 := by rw [const_expS]; norm_num
  -- the exact identity
  have hid : F ^ N = C * expS ((N : ℚ) • l) := by
    apply eq_of_logS_eq
    · rw [map_pow]; exact pow_ne_zero _ hF0
    · rw [map_mul]; exact mul_ne_zero hC0 hE0
    · rw [logS_pow hF0, logS_mul hC0 hE0, hC, logS_pow hPF, logS_Phi hp0 hF0,
        logS_expS hNl0, hl, Lser, hNm]
      push_cast
      rw [smul_sub, smul_smul, mul_comm (p : ℚ) (m : ℚ), mul_assoc, mul_inv_cancel₀ hpq,
        mul_one]
      abel
    · rw [map_pow, map_mul, hF1, hC, map_pow, const_Phi, hF1, const_expS]; simp
  -- the remainder
  set R := expS ((N : ℚ) • l) - 1 - (N : ℚ) • l with hR
  have hRi : ∀ d, pint p (coeff d R / (p : ℚ) ^ (2 * r)) := by
    intro d
    have hsum := coeff_expS hNl0 d (M := deg d + 1) (by omega)
    rw [show deg d + 1 + 1 = deg d + 2 by ring, Finset.sum_range_succ', Finset.sum_range_succ']
      at hsum
    have hcR : coeff d R = ∑ j ∈ Finset.range (deg d),
        coeff d (((N : ℚ) • l) ^ (j + 2)) / ((j + 2).factorial : ℚ) := by
      rw [hR, map_sub, map_sub, hsum]
      simp
    rw [hcR, Finset.sum_div]
    apply pint_sum hp
    intro j _
    rw [smul_pow, coeff_smul]
    have : (N : ℚ) ^ (j + 2) * coeff d (l ^ (j + 2)) / ((j + 2).factorial : ℚ) /
        (p : ℚ) ^ (2 * r) = (((n * p ^ r : ℕ) : ℚ) ^ (j + 2) / ((j + 2).factorial : ℚ) /
        (p : ℚ) ^ (2 * r)) * coeff d (l ^ (j + 2)) := by
      rw [hN]; ring
    rw [this]
    exact pint_mul hp (pint_pow_div_factorial hp hp5 n r (j + 2) hr (by omega))
      (PInt_pow hp hli _ d)
  -- diagonal coefficients
  have hdiag : coeff (bideg N) C = coeff (bideg m) (F ^ m) := by
    rw [hC, ← map_pow, hNm, bideg_mul, Phi, coeff_expand_smul]
  -- D_i C = N • integral
  have hDC : ∀ i, D i C = (N : ℚ) • Phi p hp0 (F ^ (m - 1) * D i F) := by
    intro i
    rw [hC, ← map_pow, D_Phi, D_pow, map_mul, map_mul, map_natCast, hNm]
    rw [show ((m : ℕ) : PS) = algebraMap ℚ PS (m : ℚ) by simp, ← Algebra.smul_def,
      smul_mul_assoc, smul_smul, map_mul]
    push_cast; ring_nf
  have hYi : ∀ i, PInt p (Phi p hp0 (F ^ (m - 1) * D i F)) := fun i =>
    PInt_Phi hp (PInt_mul hp (PInt_pow hp hFi _) (PInt_D hp i hFi))
  obtain ⟨q0, hq0, e0⟩ := coeff_mul_D_diag hp 0 N C A _ hCi hA (hYi 0) (hDC 0)
  obtain ⟨q1, hq1, e1⟩ := coeff_mul_D_diag hp 1 N C B _ hCi hB (hYi 1) (hDC 1)
  have hE : expS ((N : ℚ) • l) = 1 + (N : ℚ) • l + R := by rw [hR]; abel
  have hFN : F ^ N = C + (N : ℚ) • (C * l) + C * R := by
    rw [hid, hE, mul_add, mul_add, mul_one, mul_smul_comm]
  have hCl : coeff (bideg N) (C * l) = (N : ℚ) * (q0 + q1) := by
    rw [hKEY, mul_add, map_add, e0, e1]; ring
  have hmain : coeff (bideg N) (F ^ N) = coeff (bideg N) C
      + (N : ℚ) * ((N : ℚ) * (q0 + q1)) + coeff (bideg N) (C * R) := by
    rw [hFN, map_add, map_add, coeff_smul, hCl]
  rw [hmain, hdiag]
  have hfin : (coeff (bideg m) (F ^ m) + (N : ℚ) * ((N : ℚ) * (q0 + q1)) + coeff (bideg N) (C * R)
      - coeff (bideg m) (F ^ m)) / (p : ℚ) ^ (2 * r)
      = ((n ^ 2 : ℕ) : ℚ) * (q0 + q1) + coeff (bideg N) (C * R) / (p : ℚ) ^ (2 * r) := by
    rw [hN]; push_cast
    have : ((p : ℚ) ^ (2 * r)) ≠ 0 := pow_ne_zero _ hpq
    field_simp
    ring
  rw [hfin]
  refine pint_add hp (pint_mul hp (pint_nat hp _) (pint_add hp hq0 hq1)) ?_
  rw [coeff_mul, Finset.sum_div]
  apply pint_sum hp
  intro x _
  rw [mul_div_assoc]
  exact pint_mul hp (hCi _) (hRi _)

end main

end A094061
