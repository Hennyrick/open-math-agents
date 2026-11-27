import FormalConjectures.Wikipedia.BealConjecture

-- If a prime divides a power of a base, it already divides the original base.
-- We can therefore absorb exponent factors into the bases before looking
-- for a common prime. Exponents with no odd prime divisor reduce to four.
namespace OMA.R_BealConjecture_beal_conjecture_R1

/-- Signatures consisting entirely of odd primes. -/
def H1 : Prop :=
  ∀ {A B C x y z : ℕ}, A ≠ 0 → B ≠ 0 → C ≠ 0 →
    (2 < x ∧ x.Prime) → (2 < y ∧ y.Prime) → (2 < z ∧ z.Prime) →
    A ^ x + B ^ y = C ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- Signatures containing a fourth power, with all other exponents
either four or odd primes. -/
def H2 : Prop :=
  ∀ {A B C x y z : ℕ}, A ≠ 0 → B ≠ 0 → C ≠ 0 →
    (x = 4 ∨ (2 < x ∧ x.Prime)) → (y = 4 ∨ (2 < y ∧ y.Prime)) →
    (z = 4 ∨ (2 < z ∧ z.Prime)) → (x = 4 ∨ y = 4 ∨ z = 4) →
    A ^ x + B ^ y = C ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

lemma reduced_exponent {n : ℕ} (hn : 2 < n) :
    ∃ e k : ℕ, n = k * e ∧ (e = 4 ∨ (2 < e ∧ e.Prime)) := by
  by_cases h4 : 4 ∣ n
  · obtain ⟨k, hk⟩ := h4
    exact ⟨4, k, by omega, Or.inl rfl⟩
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, hm⟩ := h2
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    have hpne : p ≠ 2 := by
      rintro rfl
      omega
    obtain ⟨j, hj⟩ := hpm
    refine ⟨p, 2 * j, ?_, Or.inr ⟨lt_of_le_of_ne hp.two_le (Ne.symm hpne), hp⟩⟩
    rw [hm, hj]
    ac_rfl
  · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hpne : p ≠ 2 := by
      rintro rfl
      exact h2 hpn
    obtain ⟨j, hj⟩ := hpn
    exact ⟨p, j, hj.trans (Nat.mul_comm _ _),
      Or.inr ⟨lt_of_le_of_ne hp.two_le (Ne.symm hpne), hp⟩⟩

theorem main : H1 → H2 → type_of% @BealConjecture.beal_conjecture := by
  intro h1 h2 A B C x y z hA hB hC hx hy hz heq
  obtain ⟨r, i, rfl, hr⟩ := reduced_exponent hx
  obtain ⟨s, j, rfl, hs⟩ := reduced_exponent hy
  obtain ⟨t, k, rfl, ht⟩ := reduced_exponent hz
  rw [pow_mul, pow_mul, pow_mul] at heq
  have h : ∃ p : ℕ, p.Prime ∧ p ∣ A ^ i ∧ p ∣ B ^ j ∧ p ∣ C ^ k := by
    by_cases hfour : r = 4 ∨ s = 4 ∨ t = 4
    · exact h2 (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC) hr hs ht hfour heq
    · exact h1 (pow_ne_zero _ hA) (pow_ne_zero _ hB) (pow_ne_zero _ hC)
        (hr.resolve_left (fun h => hfour (Or.inl h)))
        (hs.resolve_left (fun h => hfour (Or.inr (Or.inl h))))
        (ht.resolve_left (fun h => hfour (Or.inr (Or.inr h)))) heq
  obtain ⟨p, hp, hpa, hpb, hpc⟩ := h
  have hd : p ∣ Finset.gcd {A, B, C} id := by
    apply Finset.dvd_gcd
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hp.dvd_of_dvd_pow hpa
    · exact hp.dvd_of_dvd_pow hpb
    · exact hp.dvd_of_dvd_pow hpc
  have hpos : Finset.gcd {A, B, C} id ≠ 0 :=
    Finset.gcd_ne_zero_iff.mpr ⟨A, Finset.mem_insert_self _ _, hA⟩
  exact hp.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd)

end OMA.R_BealConjecture_beal_conjecture_R1
