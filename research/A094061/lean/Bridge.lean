import OMAStatements.S_oeis_a094061
import Mathlib

/-!
Bridge for A094061: the number of closed king walks equals a coefficient of a power of
K = (1 + x + x^2)(1 + y + y^2) - x y.
-/

namespace A094061

open MvPolynomial Finset

/-- Exponent vector of a king move shifted by (1,1). -/
noncomputable def ex (m : ℤ × ℤ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m.1 + 1).toNat + Finsupp.single 1 (m.2 + 1).toNat

/-- The shifted step polynomial. -/
noncomputable def Kp : MvPolynomial (Fin 2) ℤ :=
  ∑ m ∈ OMA.S_oeis_a094061.moves, monomial (ex m) 1

lemma Kp_pow (n : ℕ) :
    Kp ^ n = ∑ f ∈ Fintype.piFinset (fun _ : Fin n => OMA.S_oeis_a094061.moves),
      monomial (∑ i, ex (f i)) 1 := by
  have h1 : Kp ^ n = ∏ _i : Fin n, Kp := by simp [Finset.prod_const]
  rw [h1, Kp, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [MvPolynomial.monomial_sum_one]

lemma moves_bounds {m : ℤ × ℤ} (hm : m ∈ OMA.S_oeis_a094061.moves) :
    0 ≤ m.1 + 1 ∧ 0 ≤ m.2 + 1 := by
  simp only [OMA.S_oeis_a094061.moves, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h <;> subst h <;> norm_num

lemma ex_sum_iff (n : ℕ) (f : Fin n → ℤ × ℤ) (hf : ∀ i, f i ∈ OMA.S_oeis_a094061.moves) :
    (∑ i, ex (f i)) = Finsupp.single 0 n + Finsupp.single 1 n ↔ ∑ i, f i = 0 := by
  have c1 : ∀ i, (((f i).1 + 1).toNat : ℤ) = (f i).1 + 1 :=
    fun i => Int.toNat_of_nonneg (moves_bounds (hf i)).1
  have c2 : ∀ i, (((f i).2 + 1).toNat : ℤ) = (f i).2 + 1 :=
    fun i => Int.toNat_of_nonneg (moves_bounds (hf i)).2
  have e0 : (∑ i, ex (f i)) 0 = ∑ i, ((f i).1 + 1).toNat := by
    rw [Finsupp.finsetSum_apply]; simp [ex]
  have e1 : (∑ i, ex (f i)) 1 = ∑ i, ((f i).2 + 1).toNat := by
    rw [Finsupp.finsetSum_apply]; simp [ex]
  constructor
  · intro h
    have h0 := congrArg (fun g => g 0) h
    have h1 := congrArg (fun g => g 1) h
    simp only [e0, e1] at h0 h1
    simp at h0 h1
    have h0' : ((∑ i, ((f i).1 + 1).toNat : ℕ) : ℤ) = n := by exact_mod_cast h0
    have h1' : ((∑ i, ((f i).2 + 1).toNat : ℕ) : ℤ) = n := by exact_mod_cast h1
    push_cast at h0' h1'
    simp only [c1, c2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin] at h0' h1'
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; simp at h0' ⊢; linarith
    · rw [Prod.snd_sum]; simp at h1' ⊢; linarith
  · intro h
    have h0 : ∑ i, (f i).1 = 0 := by rw [← Prod.fst_sum, h]; rfl
    have h1 : ∑ i, (f i).2 = 0 := by rw [← Prod.snd_sum, h]; rfl
    ext j
    fin_cases j
    · show (∑ i, ex (f i)) 0 = (Finsupp.single 0 n + Finsupp.single 1 n : Fin 2 →₀ ℕ) 0
      rw [e0]
      have : ((∑ i, ((f i).1 + 1).toNat : ℕ) : ℤ) = n := by
        push_cast; simp only [c1, Finset.sum_add_distrib, h0]; simp
      simp; exact_mod_cast this
    · show (∑ i, ex (f i)) 1 = (Finsupp.single 0 n + Finsupp.single 1 n : Fin 2 →₀ ℕ) 1
      rw [e1]
      have : ((∑ i, ((f i).2 + 1).toNat : ℕ) : ℤ) = n := by
        push_cast; simp only [c2, Finset.sum_add_distrib, h1]; simp
      simp; exact_mod_cast this

theorem a_eq_coeff (n : ℕ) :
    (OMA.S_oeis_a094061.a n : ℤ) = coeff (Finsupp.single 0 n + Finsupp.single 1 n) (Kp ^ n) := by
  rw [Kp_pow, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole]
  simp only [OMA.S_oeis_a094061.a]
  congr 1
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hf, h⟩
    refine ⟨hf, ?_⟩
    rw [Fintype.mem_piFinset] at hf
    exact (ex_sum_iff n f hf).2 h
  · rintro ⟨hf, h⟩
    refine ⟨hf, ?_⟩
    rw [Fintype.mem_piFinset] at hf
    exact (ex_sum_iff n f hf).1 h

theorem Kp_eq : Kp = (1 + X 0 + X 0 ^ 2) * (1 + X 1 + X 1 ^ 2) - X 0 * X 1 := by
  simp [Kp, OMA.S_oeis_a094061.moves, ex, Finset.sum_insert, monomial_eq]
  ring

end A094061
