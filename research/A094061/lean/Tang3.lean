import A094061Dev.Tang2

/-!
The tangential Steinberg lemma, part 2: truncation and integrality.
-/

namespace A094061

open PowerSeries

lemma TQ_mono {K : ℕ} {f g : PK} (h : TQ (K + 1) f g) : TQ K f g :=
  (pow_dvd_pow X (by omega)).trans h

section claimAC
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ Uc : KK) (u : PK) (hu1 : constantCoeff u = 1)

/-- The Steinberg pairing `E(f, 1 - f)` for `f = κ z u`, with `U(κ) = Uc`. -/
noncomputable def Epair : PK :=
  (C Uc + UU hp h3 u) * ld1 (1 - ff κ u) - UU hp h3 (1 - ff κ u) * (1 + phi1 p hp.ne_zero h3 (ld1 u))

include hu1

lemma Epair_eq : Epair hp h3 κ Uc u = (C Uc + UU hp h3 u) * (-(ell u * (thk 2 Li2).subst (ff κ u)))
    - (-(thk 1 Li2).subst (ff κ u) + (p : KK)⁻¹ • (thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))))
      * (ell u - E1 (UU hp h3 u)) := by
  rw [Epair, ld1_one_sub_ff hp κ u hu1, UU_one_sub_ff hp h3 κ u hu1, ← phi_ell hp h3 u, ell, map_add,
    map_one]

lemma taylor_SS (N : ℕ) : TQ (N + 1) ((thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))))
    (SS hp h3 κ u N) := by
  have ht : constantCoeff (lg (thq hp h3 u)) = 0 := const_lg _
  refine (taylor (thk 1 Li2) (const_ww h3 κ u hp.ne_zero) ht (N + 1)).trans ?_
  rw [SS]
  apply TQ_of_coeff
  intro n _
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lg_thq hp h3 u hu1, thk_add, RR, neg_pow, smul_pow, smul_eq_C_mul, aa]
  rw [show k + 1 = 1 + k by ring]
  simp only [map_mul, map_pow, map_neg, map_one, div_eq_mul_inv, map_natCast]
  ring

lemma TQ_E1H (N : ℕ) : TQ N (E1 (H1 h3 κ Uc u + H2 hp h3 κ u + H3 hp h3 κ u N))
    (Epair hp h3 κ Uc u) := by
  rw [main_identity hp h3 κ Uc u hu1 N, Epair_eq hp h3 κ Uc u hu1]
  have hU0 : constantCoeff (UU hp h3 u) = 0 := const_UU hp h3 u
  have hb : TQ N (C (aa p (N + 1) / p) * UU hp h3 u ^ (N + 1) * E1 (UU hp h3 u) * RR h3 κ u (N + 2)) 0 := by
    have := (TQ_zero_of_pow hU0 (K := N) (d := N + 1) (by omega))
    have h2 := (TQ.refl N (C (aa p (N + 1) / p))).mul (this.mul (TQ.refl N (E1 (UU hp h3 u) * RR h3 κ u (N + 2))))
    simpa [mul_assoc] using h2
  have ht := TQ_mono (taylor_SS hp h3 κ u hu1 N)
  have hE : TQ N (Ep' hp h3 κ Uc u N) ((C Uc + UU hp h3 u) * (-(ell u * (thk 2 Li2).subst (ff κ u)))
      - (-(thk 1 Li2).subst (ff κ u) + (p : KK)⁻¹ • (thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))))
        * (ell u - E1 (UU hp h3 u))) := by
    rw [Ep', smul_eq_C_mul]
    exact (TQ.refl _ _).sub (((TQ.refl _ _).add ((TQ.refl _ _).mul ht.symm)).mul (TQ.refl _ _))
  have := (hE.sub hb)
  simpa using this

end claimAC

/-! Coefficients of `A(cX)` and `A(cX^p)`, and composition. -/

lemma coeff_subst_CX (A : PK) (c : KK) (d : ℕ) : coeff d (A.subst (C c * X)) = c ^ d * coeff d A := by
  rw [coeff_subst_range A (by simp)]
  rw [Finset.sum_eq_single d]
  · rw [mul_pow, ← map_pow, coeff_C_mul, coeff_X_pow, if_pos rfl]; ring
  · intro e _ he
    rw [mul_pow, ← map_pow, coeff_C_mul, coeff_X_pow, if_neg (Ne.symm he)]; ring
  · intro h; simp at h

lemma coeff_subst_CXp {p : ℕ} (hp0 : p ≠ 0) (A : PK) (c : KK) (d : ℕ) :
    coeff d (A.subst (C c * X ^ p)) = if p ∣ d then c ^ (d / p) * coeff (d / p) A else 0 := by
  rw [coeff_subst_range A (by simp [zero_pow hp0])]
  have hterm : ∀ e, coeff e A * coeff d ((C c * X ^ p) ^ e) =
      if d = p * e then c ^ e * coeff e A else 0 := by
    intro e
    rw [mul_pow, ← map_pow, ← pow_mul, coeff_C_mul, coeff_X_pow]
    split_ifs <;> ring
  simp only [hterm]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp0)]
    · intro e _ he
      rw [if_neg]; intro h'; exact he (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) h').symm
    · intro hm; exfalso; apply hm; simp
      rcases m with _ | m
      · omega
      · nlinarith [Nat.pos_of_ne_zero hp0]
  · apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]; rintro rfl; exact h (dvd_mul_right p e)

lemma subst_comp_CX (A : PK) (c : KK) {g : PK} (hg : constantCoeff g = 0) :
    PowerSeries.subst g (PowerSeries.subst (C c * X) A) = A.subst (C c * g) := by
  have ha : HasSubst (C c * X : PK) := HasSubst.of_constantCoeff_zero' (by simp)
  have hb : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [subst_comp_subst_apply ha hb, subst_mul hb, subst_X hb, PowerSeries.subst_C]
  rfl

lemma subst_comp_CXp {p : ℕ} (hp0 : p ≠ 0) (A : PK) (c : KK) {g : PK} (hg : constantCoeff g = 0) :
    PowerSeries.subst g (PowerSeries.subst (C c * X ^ p) A) = A.subst (C c * g ^ p) := by
  have ha : HasSubst (C c * X ^ p : PK) := HasSubst.of_constantCoeff_zero' (by simp [zero_pow hp0])
  have hb : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [subst_comp_subst_apply ha hb, subst_mul hb, subst_pow hb, subst_X hb, PowerSeries.subst_C]
  rfl

/-- `p^k / (k+2)!` is `p`-integral for `p ≥ 5`. -/
lemma pint_pk_fact {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℕ) :
    pint p ((p : ℚ) ^ k / ((k + 2).factorial : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p (k + 2).factorial with hv
  have hlt : (p - 1) * v < k + 2 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have hvk : v ≤ k := by
    have : 4 * v ≤ (p - 1) * v := Nat.mul_le_mul_right v (by omega)
    omega
  have hfac : (k + 2).factorial = p ^ v * ordCompl[p] (k + 2).factorial := by
    rw [hv, ← Nat.factorization_def _ hp]; exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
  have hu : ¬ p ∣ ordCompl[p] (k + 2).factorial := Nat.not_dvd_ordCompl hp (Nat.factorial_ne_zero _)
  set u := ordCompl[p] (k + 2).factorial
  have hu0 : (u : ℚ) ≠ 0 := by
    have : u ≠ 0 := by rintro h; rw [h] at hu; exact hu (dvd_zero p)
    exact_mod_cast this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : ℚ) ^ k / ((k + 2).factorial : ℚ) = ((p ^ (k - v) : ℕ) : ℚ) * (u : ℚ)⁻¹ := by
    rw [hfac]; push_cast
    rw [show (p : ℚ) ^ k = (p : ℚ) ^ (k - v) * (p : ℚ) ^ v by rw [← pow_add, Nat.sub_add_cancel hvk]]
    field_simp
  rw [e]; exact pint_mul hp (pint_nat hp _) (pint_inv_nat hp hu)

lemma OI_inv_nat {p : ℕ} (hp : p.Prime) {d : ℕ} (hd : ¬ p ∣ d) : OI p ((d : KK)⁻¹) := by
  have := OI_rat hp (pint_inv_nat hp hd); simpa [rr] using this

section integ
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ Uc : KK) (u : PK)

/-- Hypothesis on the constant `U(κ)`: the defect at multiples of `p` is integral. -/
def TangHyp (N : ℕ) : Prop := ∀ m, 1 ≤ m → p * m ≤ N →
  OI p ((κ ^ (p * m) - (sig p h3 κ) ^ m - ((p * m : ℕ) : KK) * Uc * κ ^ (p * m)) / ((p * m : ℕ) : KK) ^ 2)

noncomputable def BB1 : PK := Li2.subst (C κ * X) - C (((p : KK) ^ 2)⁻¹) * Li2.subst (C (sig p h3 κ) * X ^ p)
  - C Uc * (thk 1 Li2).subst (C κ * X)

noncomputable def BB2 : PK := C ((p : KK)⁻¹) * (thk 1 Li2).subst (C (sig p h3 κ) * X ^ p)
  - (thk 1 Li2).subst (C κ * X)

include hp

lemma H1_eq : H1 h3 κ Uc u = PowerSeries.subst (vv u) (BB1 h3 κ Uc) := by
  have hb : HasSubst (vv u) := HasSubst.of_constantCoeff_zero' (const_vv u)
  rw [BB1, subst_sub hb, subst_sub hb, subst_mul hb, subst_mul hb, PowerSeries.subst_C,
    PowerSeries.subst_C, subst_comp_CX _ _ (const_vv u), subst_comp_CX _ _ (const_vv u),
    subst_comp_CXp hp.ne_zero _ _ (const_vv u), H1, ff, ww]
  rfl

lemma H2_eq : H2 hp h3 κ u = UU hp h3 u * PowerSeries.subst (vv u) (BB2 h3 κ) := by
  have hb : HasSubst (vv u) := HasSubst.of_constantCoeff_zero' (const_vv u)
  rw [BB2, subst_sub hb, subst_mul hb, PowerSeries.subst_C,
    subst_comp_CX _ _ (const_vv u), subst_comp_CXp hp.ne_zero _ _ (const_vv u), H2, ff, ww]
  show _ = UU hp h3 u * (C ((p : KK)⁻¹) * _ - _)
  ring

end integ

section final
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ Uc : KK) (u : PK)
include hp

lemma coeff_Li2_ne {d : ℕ} (hd : d ≠ 0) : coeff d Li2 = ((d : KK) ^ 2)⁻¹ := by
  simp [Li2, hd]

lemma coeff_thk1_ne {d : ℕ} (hd : d ≠ 0) : coeff d (thk 1 Li2) = (d : KK)⁻¹ := by
  rw [coeff_thk1_Li2, if_neg hd]

omit hp in
lemma OI_BB1 (hκ : OI p κ) (hUc : OI p Uc) (hp : p.Prime) (N : ℕ) (hyp : TangHyp h3 κ Uc N) :
    ∀ d ≤ N, OI p (coeff d (BB1 h3 κ Uc)) := by
  intro d hdN
  have hpK := pKK_ne hp
  rw [BB1, map_sub, map_sub, coeff_C_mul, coeff_C_mul, coeff_subst_CX, coeff_subst_CX,
    coeff_subst_CXp hp.ne_zero]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp [Li2, thk]; exact OI_zero hp
  by_cases hpd : p ∣ d
  · obtain ⟨m, rfl⟩ := hpd
    have hm : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hd0)
    have hm0 : m ≠ 0 := by omega
    have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp.ne_zero),
      coeff_Li2_ne hp hpm0, coeff_Li2_ne hp hm0, coeff_thk1_ne hp hpm0]
    have e : κ ^ (p * m) * (((p * m : ℕ) : KK) ^ 2)⁻¹ - ((p : KK) ^ 2)⁻¹ * ((sig p h3 κ) ^ m
        * ((m : KK) ^ 2)⁻¹) - Uc * (κ ^ (p * m) * ((p * m : ℕ) : KK)⁻¹) =
        (κ ^ (p * m) - (sig p h3 κ) ^ m - ((p * m : ℕ) : KK) * Uc * κ ^ (p * m))
          / ((p * m : ℕ) : KK) ^ 2 := by
      have hm' : (m : KK) ≠ 0 := by exact_mod_cast hm0
      push_cast; field_simp
    rw [e]; exact hyp m hm hdN
  · rw [if_neg hpd, coeff_Li2_ne hp (by omega), coeff_thk1_ne hp (by omega), mul_zero, sub_zero]
    have hi := OI_inv_nat hp hpd
    refine OI_sub hp (OI_mul hp (OI_pow hp hκ d) ?_) (OI_mul hp hUc (OI_mul hp (OI_pow hp hκ d) hi))
    rw [← inv_pow]; exact OI_pow hp hi 2

omit hp in
lemma OI_BB2 (hκ : OI p κ) (hUc : OI p Uc) (hp : p.Prime) (N : ℕ) (hyp : TangHyp h3 κ Uc N) :
    ∀ d ≤ N, OI p (coeff d (BB2 h3 κ)) := by
  intro d hdN
  have hpK := pKK_ne hp
  rw [BB2, map_sub, coeff_C_mul, coeff_subst_CX, coeff_subst_CXp hp.ne_zero]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp [Li2, thk]; exact OI_zero hp
  by_cases hpd : p ∣ d
  · obtain ⟨m, rfl⟩ := hpd
    have hm : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hd0)
    have hm0 : m ≠ 0 := by omega
    have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp.ne_zero),
      coeff_thk1_ne hp hpm0, coeff_thk1_ne hp hm0]
    set Q := (κ ^ (p * m) - (sig p h3 κ) ^ m - ((p * m : ℕ) : KK) * Uc * κ ^ (p * m))
      / ((p * m : ℕ) : KK) ^ 2 with hQ
    have e : (p : KK)⁻¹ * ((sig p h3 κ) ^ m * (m : KK)⁻¹) - κ ^ (p * m) * ((p * m : ℕ) : KK)⁻¹ =
        -(Q * ((p * m : ℕ) : KK) + Uc * κ ^ (p * m)) := by
      have hm' : (m : KK) ≠ 0 := by exact_mod_cast hm0
      rw [hQ]; push_cast; field_simp; ring
    rw [e]
    exact OI_neg hp (OI_add hp (OI_mul hp (hyp m hm hdN) (OI_nat hp _)) (OI_mul hp hUc (OI_pow hp hκ _)))
  · rw [if_neg hpd, coeff_thk1_ne hp (by omega), mul_zero, zero_sub]
    exact OI_neg hp (OI_mul hp (OI_pow hp hκ d) (OI_inv_nat hp hpd))

/-- **Tangential Steinberg lemma.** For `f = κ z u` and a constant `U(κ) = Uc` satisfying the
defect hypothesis up to degree `N`, the pairing `E(f, 1 - f)` is an Euler derivative of an
integral series in all degrees `1 ≤ n ≤ N`. -/
theorem tangential (hp5 : 5 ≤ p) (hκ : OI p κ) (hUc : OI p Uc) (hu1 : constantCoeff u = 1)
    (hu : OIs p u) (N : ℕ) (hyp : TangHyp h3 κ Uc N) :
    ∀ n, 1 ≤ n → n ≤ N → OI p (coeff n (Epair hp h3 κ Uc u) / n) := by
  intro n hn1 hnN
  set H := H1 h3 κ Uc u + H2 hp h3 κ u + H3 hp h3 κ u N with hH
  have hc : coeff n (Epair hp h3 κ Uc u) = (n : KK) * coeff n H := by
    rw [← TQ_coeff (TQ_E1H hp h3 κ Uc u hu1 N) hnN, coeff_E1]
  have hn0 : (n : KK) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [hc, mul_div_cancel_left₀ _ hn0, hH, map_add, map_add]
  have hv0 := const_vv u
  have hvi : OIs p (vv u) := OIs_mul hp (OIs_X hp) hu
  have hUi : OIs p (UU hp h3 u) := OIs_UU hp h3 hu1 hu
  refine OI_add hp (OI_add hp ?_ ?_) ?_
  · rw [H1_eq hp h3 κ Uc u, coeff_subst_range _ hv0]
    exact OI_sum hp _ _ (fun d hd => OI_mul hp
      (OI_BB1 h3 κ Uc hκ hUc hp N hyp d (by simp at hd; omega)) (OIs_pow hp hvi d n))
  · rw [H2_eq hp h3 κ u, coeff_mul]
    refine OI_sum hp _ _ (fun x hx => OI_mul hp (hUi _) ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_subst_range _ hv0]
    exact OI_sum hp _ _ (fun d hd => OI_mul hp
      (OI_BB2 h3 κ Uc hκ hUc hp N hyp d (by simp at hd; omega)) (OIs_pow hp hvi d _))
  · have hwi : OIs p (ww h3 κ u) := OIs_mul hp (OIs_C hp (OI_sig hp h3 hκ)) (OIs_pow hp hvi p)
    have : OIs p (H3 hp h3 κ u N) := by
      rw [H3]
      refine OIs_neg hp (OIs_sum hp _ _ (fun k _ => OIs_mul hp (OIs_mul hp (OIs_C hp ?_)
        (OIs_pow hp hUi _)) (OIs_subst hp (OIs_thk_Li2 hp (k + 2) (by omega))
          (const_ww h3 κ u hp.ne_zero) hwi)))
      have e : aa p (k + 2) / (p : KK) ^ 2 = rr ((-1) ^ (k + 2) * ((p : ℚ) ^ k / ((k + 2).factorial : ℚ))) := by
        simp only [aa, rr, map_mul, map_pow, map_neg, map_one, map_div₀, map_natCast]
        have := pKK_ne hp
        have hf : ((k + 2).factorial : KK) ≠ 0 := by exact_mod_cast (k + 2).factorial_ne_zero
        rw [neg_pow]; field_simp; ring
      rw [e]
      exact OI_rat hp (pint_mul hp (by simpa using pint_int hp ((-1) ^ (k + 2))) (pint_pk_fact hp hp5 k))
    exact this n

end final

end A094061
