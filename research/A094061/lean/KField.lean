import A094061Dev.Series2

/-!
The field `ℚ(ω)`, `ω^2 + ω + 1 = 0`, with `p`-integrality and the Frobenius automorphism
`σ(ω) = ω^p`.
-/

namespace A094061

open Polynomial

/-- `X^2 + X + 1`. -/
noncomputable def cyc : ℚ[X] := X ^ 2 + X + 1

instance : Fact (Irreducible cyc) := ⟨by
  have := cyclotomic.irreducible_rat (n := 3) (by norm_num)
  rwa [cyclotomic_three] at this⟩

/-- `ℚ(ω)`. -/
abbrev KK := AdjoinRoot cyc

/-- A primitive cube root of unity. -/
noncomputable def om : KK := AdjoinRoot.root cyc

lemma om_rel : om ^ 2 + om + 1 = 0 := by
  have h : AdjoinRoot.mk cyc cyc = 0 := AdjoinRoot.mk_self
  have e : AdjoinRoot.mk cyc cyc = om ^ 2 + om + 1 := by
    show AdjoinRoot.mk cyc (X ^ 2 + X + 1) = om ^ 2 + om + 1
    simp [om, AdjoinRoot.mk_X]
  rw [← e]; exact h

lemma om_sq : om ^ 2 = -om - 1 := by linear_combination om_rel

lemma om_cube : om ^ 3 = 1 := by linear_combination (om - 1) * om_rel

/-- Rational embedding. -/
noncomputable abbrev rr (q : ℚ) : KK := algebraMap ℚ KK q

lemma om_not_rat (q : ℚ) : om ≠ rr q := by
  intro h
  have h2 := om_rel
  rw [h] at h2
  have : rr (q ^ 2 + q + 1) = rr 0 := by simp [rr] at h2 ⊢; exact h2
  have h3 := (algebraMap ℚ KK).injective this
  nlinarith [sq_nonneg (2 * q + 1)]

lemma coord_unique {a b c d : ℚ} (h : rr a + rr b * om = rr c + rr d * om) : a = c ∧ b = d := by
  by_cases hbd : b = d
  · subst hbd
    refine ⟨(algebraMap ℚ KK).injective ?_, rfl⟩
    simpa using h
  · exfalso
    apply om_not_rat ((c - a) / (b - d))
    have hne : rr (b - d) ≠ 0 := by
      simp [rr, sub_eq_zero]; exact hbd
    have e : rr (b - d) * om = rr (c - a) := by
      simp only [rr, map_sub] at h ⊢; linear_combination h
    rw [show rr ((c - a) / (b - d)) = rr (c - a) / rr (b - d) by simp [rr], ← e]
    field_simp

/-- `p`-integral elements `a + b ω`. -/
def OI (p : ℕ) (x : KK) : Prop := ∃ a b : ℚ, pint p a ∧ pint p b ∧ x = rr a + rr b * om

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma OI_rat {q : ℚ} (hq : pint p q) : OI p (rr q) :=
  ⟨q, 0, hq, pint_zero hp, by simp⟩

lemma OI_om : OI p om := ⟨0, 1, pint_zero hp, by simpa using pint_nat hp 1, by simp⟩

lemma OI_zero : OI p 0 := by simpa using OI_rat hp (pint_zero hp)

lemma OI_one : OI p 1 := by simpa using OI_rat hp (pint_nat hp 1)

lemma OI_add {x y : KK} (hx : OI p x) (hy : OI p y) : OI p (x + y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  exact ⟨a + c, b + d, pint_add hp ha hc, pint_add hp hb hd, by simp [rr]; ring⟩

lemma OI_neg {x : KK} (hx : OI p x) : OI p (-x) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  exact ⟨-a, -b, pint_neg ha, pint_neg hb, by simp [rr]; ring⟩

lemma OI_sub {x y : KK} (hx : OI p x) (hy : OI p y) : OI p (x - y) := by
  rw [sub_eq_add_neg]; exact OI_add hp hx (OI_neg hp hy)

lemma OI_mul {x y : KK} (hx : OI p x) (hy : OI p y) : OI p (x * y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  refine ⟨a * c - b * d, a * d + b * c - b * d,
    pint_sub hp (pint_mul hp ha hc) (pint_mul hp hb hd),
    pint_sub hp (pint_add hp (pint_mul hp ha hd) (pint_mul hp hb hc)) (pint_mul hp hb hd), ?_⟩
  simp only [rr, map_sub, map_add, map_mul]
  linear_combination ((algebraMap ℚ KK b) * (algebraMap ℚ KK d)) * om_rel

lemma OI_pow {x : KK} (hx : OI p x) (n : ℕ) : OI p (x ^ n) := by
  induction n with
  | zero => simpa using OI_one hp
  | succ n ih => rw [pow_succ]; exact OI_mul hp ih hx

lemma OI_nat (n : ℕ) : OI p (n : KK) := by
  have := OI_rat hp (pint_nat hp n); simpa [rr] using this

lemma OI_int (n : ℤ) : OI p (n : KK) := by
  have := OI_rat hp (pint_int hp n); simpa [rr] using this

lemma OI_sum {ι : Type*} (s : Finset ι) (f : ι → KK) (h : ∀ i ∈ s, OI p (f i)) :
    OI p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OI_zero hp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact OI_add hp (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A rational number that is integral in `ℚ(ω)` is `p`-integral. -/
lemma pint_of_OI {q : ℚ} (h : OI p (rr q)) : pint p q := by
  obtain ⟨a, b, ha, _, e⟩ := h
  have := coord_unique (a := q) (b := 0) (c := a) (d := b) (by simpa using e)
  rw [this.1]; exact ha

end

/-- Fermat for `p`-integral rationals. -/
lemma pint_fermat {p : ℕ} (hp : p.Prime) {a : ℚ} (ha : pint p a) : pint p ((a - a ^ p) / p) := by
  have : Fact p.Prime := ⟨hp⟩
  set n := a.num; set d := a.den
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have ha' : a = n / d := (Rat.num_div_den a).symm
  set N0 : ℤ := n * (d : ℤ) ^ (p - 1) - n ^ p
  have hN0 : (p : ℤ) ∣ N0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hdz : ((d : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]; exact ha
    simp only [N0, Int.cast_sub, Int.cast_mul, Int.cast_pow, ZMod.pow_card,
      ZMod.pow_card_sub_one_eq_one hdz, mul_one, sub_self]
  obtain ⟨t, ht⟩ := hN0
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : 1 ≤ p := hp.one_lt.le
  have key : (a - a ^ p) / p = (t : ℚ) * ((d ^ p : ℕ) : ℚ)⁻¹ := by
    have e : (N0 : ℚ) = (p : ℚ) * t := by exact_mod_cast ht
    simp only [N0] at e
    rw [ha']
    push_cast at e ⊢
    have e2 : (d : ℚ) ^ p = (d : ℚ) ^ (p - 1) * d := by
      rw [← pow_succ, Nat.sub_add_cancel hp1]
    field_simp
    rw [div_pow, e2]
    field_simp
    linear_combination e
  rw [key]
  refine pint_mul hp (pint_int hp t) (pint_inv_nat hp ?_)
  intro h; exact ha (hp.dvd_of_dvd_pow h)

lemma OI_div_binom_aux (q : ℕ) (hp : (q + 1).Prime) {u v : KK} (hu : OI (q + 1) u)
    (hv : OI (q + 1) v) :
    OI (q + 1) (((u + v) ^ (q + 1) - u ^ (q + 1) - v ^ (q + 1)) / ((q + 1 : ℕ) : KK)) := by
  have hp0 : ((q + 1 : ℕ) : KK) ≠ 0 := by
    have : ((q + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (q + 1).succ_ne_zero
    simpa [rr] using (map_ne_zero (algebraMap ℚ KK)).2 this
  set c : ℕ → KK := fun k => (((q + 1).choose (k + 1) / (q + 1) : ℕ) : KK)
  have e : ∀ k ∈ Finset.range q, u ^ (k + 1) * v ^ (q + 1 - (k + 1)) * ((q + 1).choose (k + 1) : KK)
      = ((q + 1 : ℕ) : KK) * (u ^ (k + 1) * v ^ (q + 1 - (k + 1)) * c k) := by
    intro k hk
    have hdv : (q + 1) ∣ (q + 1).choose (k + 1) :=
      hp.dvd_choose_self (by omega) (by simp at hk; omega)
    obtain ⟨t, ht⟩ := hdv
    simp only [c, ht, Nat.mul_div_cancel_left t (Nat.succ_pos q)]
    push_cast; ring
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, Nat.choose_zero_right,
    one_mul, Nat.sub_zero]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have : (((q + 1 : ℕ) : KK) * ∑ k ∈ Finset.range q, u ^ (k + 1) * v ^ (q + 1 - (k + 1)) * c k
      + v ^ (q + 1) + u ^ (q + 1) - u ^ (q + 1) - v ^ (q + 1)) / ((q + 1 : ℕ) : KK)
      = ∑ k ∈ Finset.range q, u ^ (k + 1) * v ^ (q + 1 - (k + 1)) * c k := by
    field_simp; ring
  rw [this]
  apply OI_sum hp
  intro k _
  exact OI_mul hp (OI_mul hp (OI_pow hp hu _) (OI_pow hp hv _)) (OI_nat hp _)

lemma OI_div_p_binom {p : ℕ} (hp : p.Prime) {u v : KK} (hu : OI p u) (hv : OI p v) :
    OI p (((u + v) ^ p - u ^ p - v ^ p) / p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  exact OI_div_binom_aux q hp hu hv


lemma not_three_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ 3 ∣ p := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
  omega

lemma om_pow_rel {p : ℕ} (h3 : ¬ 3 ∣ p) : (om ^ p) ^ 2 + om ^ p + 1 = 0 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, p = 3 * k + 1 ∨ p = 3 * k + 2 := by
    refine ⟨p / 3, ?_⟩; omega
  · subst hk
    rw [pow_add, pow_mul, om_cube, one_pow, one_mul, pow_one]; exact om_rel
  · subst hk
    rw [pow_add, pow_mul, om_cube, one_pow, one_mul]
    linear_combination (om ^ 2 - om + 1) * om_rel + 0 * om_cube
      + (om) * (om_cube) - om * om_cube + (om - 1 + 1) * 0

/-- Frobenius automorphism `ω ↦ ω^p`. -/
noncomputable def sig (p : ℕ) (h3 : ¬ 3 ∣ p) : KK →ₐ[ℚ] KK :=
  AdjoinRoot.liftAlgHom cyc (Algebra.ofId ℚ KK) (om ^ p) (by
    simp [cyc, aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one]
    exact om_pow_rel h3)

lemma sig_om {p : ℕ} (h3 : ¬ 3 ∣ p) : sig p h3 om = om ^ p :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma sig_rr {p : ℕ} (h3 : ¬ 3 ∣ p) (q : ℚ) : sig p h3 (rr q) = rr q := (sig p h3).commutes q

section frob2
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p)
include hp

lemma OI_sig {x : KK} (hx : OI p x) : OI p (sig p h3 x) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  rw [map_add, map_mul, sig_rr, sig_rr, sig_om]
  exact OI_add hp (OI_rat hp ha) (OI_mul hp (OI_rat hp hb) (OI_pow hp (OI_om hp) p))

lemma frob_cong {x : KK} (hx : OI p x) : OI p ((sig p h3 x - x ^ p) / p) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0 : (p : KK) ≠ 0 := by simpa [rr] using (map_ne_zero (algebraMap ℚ KK)).2 hpq
  have e : (sig p h3 (rr a + rr b * om) - (rr a + rr b * om) ^ p) / p =
      rr ((a - a ^ p) / p) + rr ((b - b ^ p) / p) * om ^ p
      - (((rr a) + (rr b * om)) ^ p - (rr a) ^ p - (rr b * om) ^ p) / p := by
    rw [map_add, map_mul, sig_rr, sig_rr, sig_om]
    simp only [rr, map_div₀, map_sub, map_pow, map_natCast]
    field_simp
    ring
  rw [e]
  refine OI_sub hp (OI_add hp (OI_rat hp (pint_fermat hp ha))
    (OI_mul hp (OI_rat hp (pint_fermat hp hb)) (OI_pow hp (OI_om hp) p))) ?_
  exact OI_div_p_binom hp (OI_rat hp ha) (OI_mul hp (OI_rat hp hb) (OI_om hp))

end frob2

end A094061
