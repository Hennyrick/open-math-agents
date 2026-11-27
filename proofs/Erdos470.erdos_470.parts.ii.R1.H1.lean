import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

-- Step Erdos470.erdos_470.parts.ii.R1.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.ii.R1
-- Credit: @Hennyrick
-- H1 := ∀ k a b : ℕ, b + 3 < a → a * (a + b) < 2 ^ (k + 2) → (2 ^ (k + 2) - a).Prime →     (2 ^ (k + 2) + b).Prime →     Erdos470.PrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b))  -- For infinitely many k there are primes 2^(k+2) - a and 2^(k+2) + b as in H1.

-- Proof (Melfi 2015, Theorem 1). Put Z = 2^k, p = 4Z - a, q = 4Z + b, n = Z p q.
-- Both a and b are odd, so a = b + 2j + 4 for some j.
-- * sigma(n) = 2n + A with A = 2Z(2j+1) + (a-1)(b+1) > 0, so n is abundant.
-- * A sum of distinct divisors of n equal to A has the form S0 + p B + q C with S0, B, C < 2Z.
--   If B + C ≤ j it is at most 2Z - 1 + q j < A; if B + C ≥ j + 1 it is at least p (j+1) > A.
--   So no subset of the proper divisors sums to n.
-- * Every proper divisor divides n/2, n/p or n/q, none of which is abundant.

namespace OMA.Erdos470H1Proof

open Finset

lemma sum_divisors_two_pow (m : ℕ) : ∑ d ∈ (2 ^ m).divisors, d = 2 ^ (m + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  have h := geom_sum_mul_add (1 : ℕ) (m + 1)
  norm_num at h
  omega

lemma sum_divisors_prime {r : ℕ} (hr : r.Prime) : ∑ d ∈ r.divisors, d = r + 1 := by
  rw [hr.divisors, Finset.sum_pair hr.one_lt.ne]
  ring

lemma cop_two_pow {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (m : ℕ) : Nat.Coprime (2 ^ m) r :=
  Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm h2))

lemma sigma_two (m : ℕ) {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) :
    ∑ d ∈ (2 ^ m * r).divisors, d = (2 ^ (m + 1) - 1) * (r + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (cop_two_pow hr h2 m), sum_divisors_two_pow,
    sum_divisors_prime hr]

lemma sigma_three (m : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ m * p * q).divisors, d = (2 ^ (m + 1) - 1) * (p + 1) * (q + 1) := by
  have hc : Nat.Coprime (2 ^ m * p) q :=
    Nat.Coprime.mul (cop_two_pow hq hq2 m) ((Nat.coprime_primes hp hq).2 hpq)
  rw [Nat.Coprime.sum_divisors_mul hc, sigma_two m hp hp2, sum_divisors_prime hq]

lemma part_sum (Z r : ℕ) (hr : 0 < r) (U : Finset ℕ) (hU : ∀ d ∈ U, r ∣ d ∧ d / r ∣ Z)
    (hZ : Z ≠ 0) :
    ∑ d ∈ U, d = r * ∑ d ∈ U, d / r ∧ ∑ d ∈ U, d / r ≤ ∑ e ∈ Z.divisors, e := by
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact (Nat.mul_div_cancel' (hU d hd).1).symm
  · rw [← Finset.sum_image (f := fun e => e) (s := U) (g := fun d => d / r) ?_]
    · apply Finset.sum_le_sum_of_subset
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨d, hd, rfl⟩ := he
      exact Nat.mem_divisors.2 ⟨(hU d hd).2, hZ⟩
    · intro x hx y hy hxy
      have hx' : x ∈ U := by simpa using hx
      have hy' : y ∈ U := by simpa using hy
      have hxy' : x / r = y / r := hxy
      calc x = x / r * r := (Nat.div_mul_cancel (hU x hx').1).symm
        _ = y / r * r := by rw [hxy']
        _ = y := Nat.div_mul_cancel (hU y hy').1

lemma decomp (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (T : Finset ℕ)
    (hT : T ⊆ (2 ^ k * p * q).divisors) (hsmall : ∀ d ∈ T, d < p * q) :
    ∃ S0 B C, S0 ≤ 2 ^ (k + 1) - 1 ∧ B ≤ 2 ^ (k + 1) - 1 ∧ C ≤ 2 ^ (k + 1) - 1 ∧
      ∑ d ∈ T, d = S0 + p * B + q * C := by
  have hZ : 2 ^ k ≠ 0 := by positivity
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hdiv : ∀ d ∈ T, d ∣ 2 ^ k * p * q ∧ 0 < d := by
    intro d hd
    have h := Nat.mem_divisors.1 (hT hd)
    exact ⟨h.1, Nat.pos_of_dvd_of_pos h.1 (Nat.pos_of_ne_zero h.2)⟩
  have hnot : ∀ d ∈ T, ¬ (p ∣ d ∧ q ∣ d) := by
    rintro d hd ⟨h1, h2⟩
    have h3 := Nat.le_of_dvd (hdiv d hd).2 (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcpq h1 h2)
    have h4 := hsmall d hd
    omega
  have h0 : ∀ d ∈ T, ¬ p ∣ d → ¬ q ∣ d → d ∣ 2 ^ k := by
    intro d hd h1 h2
    have c1 : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 h1).symm
    have c2 : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).2 h2).symm
    exact c1.dvd_of_dvd_mul_right (c2.dvd_of_dvd_mul_right (hdiv d hd).1)
  have hpd : ∀ d ∈ T, p ∣ d → d / p ∣ 2 ^ k := by
    intro d hd h1
    have h2 : ¬ q ∣ d := fun h2 => hnot d hd ⟨h1, h2⟩
    obtain ⟨e, rfl⟩ := h1
    rw [Nat.mul_div_cancel_left e hp.pos]
    have h3 : p * e ∣ p * (2 ^ k * q) := by
      have := (hdiv _ hd).1
      rwa [show 2 ^ k * p * q = p * (2 ^ k * q) by ring] at this
    have he : e ∣ 2 ^ k * q := Nat.dvd_of_mul_dvd_mul_left hp.pos h3
    have hqe : ¬ q ∣ e := fun h => h2 (Dvd.dvd.mul_left h p)
    exact ((Nat.Prime.coprime_iff_not_dvd hq).2 hqe).symm.dvd_of_dvd_mul_right he
  have hqd : ∀ d ∈ T, q ∣ d → d / q ∣ 2 ^ k := by
    intro d hd h1
    have h2 : ¬ p ∣ d := fun h2 => hnot d hd ⟨h2, h1⟩
    obtain ⟨e, rfl⟩ := h1
    rw [Nat.mul_div_cancel_left e hq.pos]
    have h3 : q * e ∣ q * (2 ^ k * p) := by
      have := (hdiv _ hd).1
      rwa [show 2 ^ k * p * q = q * (2 ^ k * p) by ring] at this
    have he : e ∣ 2 ^ k * p := Nat.dvd_of_mul_dvd_mul_left hq.pos h3
    have hpe : ¬ p ∣ e := fun h => h2 (Dvd.dvd.mul_left h q)
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpe).symm.dvd_of_dvd_mul_right he
  have e1 := Finset.sum_filter_add_sum_filter_not T (fun d => p ∣ d) (fun d => d)
  have e2 := Finset.sum_filter_add_sum_filter_not (T.filter (fun d => ¬ p ∣ d))
    (fun d => q ∣ d) (fun d => d)
  obtain ⟨hP1, hP2⟩ := part_sum (2 ^ k) p hp.pos (T.filter (fun d => p ∣ d)) (by
    intro d hd
    rw [Finset.mem_filter] at hd
    exact ⟨hd.2, hpd d hd.1 hd.2⟩) hZ
  obtain ⟨hQ1, hQ2⟩ := part_sum (2 ^ k) q hq.pos
    ((T.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d)) (by
    intro d hd
    simp only [Finset.mem_filter] at hd
    exact ⟨hd.2, hqd d hd.1.1 hd.2⟩) hZ
  obtain ⟨h01, h02⟩ := part_sum (2 ^ k) 1 one_pos
    ((T.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d)) (by
    intro d hd
    simp only [Finset.mem_filter] at hd
    refine ⟨one_dvd d, ?_⟩
    rw [Nat.div_one]
    exact h0 d hd.1.1 hd.1.2 hd.2) hZ
  rw [sum_divisors_two_pow] at hP2 hQ2 h02
  refine ⟨_, _, _, h02, hP2, hQ2, ?_⟩
  rw [← e1, ← e2, hP1, hQ1, h01]
  ring

/-- `σ(2^m r) ≤ 2 · 2^m r` when `2^(m+1) ≤ r + 1`. -/
lemma not_abundant_two (m : ℕ) {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (hbig : 2 ^ (m + 1) ≤ r + 1) :
    ¬ (2 ^ m * r).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, sigma_two m hr h2, not_lt]
  have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ (m + 1) = Y := ⟨_, rfl⟩
  have hYm : 2 * 2 ^ m = Y := by rw [← hY, pow_succ]; ring
  rw [hY] at h1 hbig ⊢
  have : 2 * (2 ^ m * r) = Y * r := by rw [← hYm]; ring
  rw [this]
  zify [h1] at hbig ⊢
  nlinarith

set_option maxHeartbeats 2000000 in
theorem melfi : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 := by
  intro k a b hab hsize hp hq
  have hX : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  have hY : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  obtain ⟨Z, hZ⟩ : ∃ Z, 2 ^ k = Z := ⟨_, rfl⟩
  rw [hZ] at hX hY
  rw [hX] at hsize hp hq ⊢
  rw [hZ]
  have ha_le : a ≤ a * (a + b) := Nat.le_mul_of_pos_right a (by omega)
  have haa : a * a ≤ a * (a + b) := Nat.mul_le_mul_left a (by omega)
  have h4a : 4 * a ≤ a * a := Nat.mul_le_mul_right a (by omega)
  have ha_lt : a < Z := by linarith
  have hZ1 : 1 ≤ Z := by omega
  generalize hpdef : 4 * Z - a = p at hp ⊢
  have hpa : p + a = 4 * Z := by omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : 4 * Z + b ≠ 2 := by omega
  have hpodd := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hqodd := Nat.odd_iff.1 (hq.odd_of_ne_two hq2)
  obtain ⟨j, rfl⟩ : ∃ j, a = b + 2 * j + 4 := ⟨(a - b - 4) / 2, by omega⟩
  have hpq : p ≠ 4 * Z + b := by omega
  have hpq' : p ≤ 4 * Z + b := by omega
  have hsize' : (b + 2 * j + 4) * (b + j + 2) * 2 < 4 * Z := by
    have e : (b + 2 * j + 4) * (b + 2 * j + 4 + b) = (b + 2 * j + 4) * (b + j + 2) * 2 := by ring
    rw [← e]; exact hsize
  have ha2 : b + 2 * j + 4 < 2 * Z := by
    have := Nat.mul_le_mul_left (b + 2 * j + 4) (show 1 ≤ b + j + 2 by omega)
    linarith
  have hp2Z : 2 * Z < p := by omega
  have e1 : (p : ℤ) = 4 * Z - (b + 2 * j + 4) := by omega
  -- the abundance: sigma(n) = 2n + A
  have key : (2 * Z - 1) * (p + 1) * (4 * Z + b + 1) =
      2 * Z * p * (4 * Z + b) + (2 * Z * (2 * j + 1) + (b + 2 * j + 3) * (b + 1)) := by
    have h2Z : 1 ≤ 2 * Z := by omega
    zify [h2Z]
    rw [e1]
    ring
  have hsig := sigma_three k hp hq hp2 hq2 hpq
  rw [hY, hZ] at hsig
  have hA_lt : 2 * Z * (2 * j + 1) + (b + 2 * j + 3) * (b + 1) < p * (4 * Z + b) := by
    have i1 : 2 * Z * (2 * j + 1) < 2 * Z * (2 * Z) := by
      apply Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have i2 : (b + 2 * j + 3) * (b + 1) < (2 * Z) * (2 * Z) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    have i3 : (2 * Z) * (4 * Z) < p * (4 * Z) := Nat.mul_lt_mul_of_pos_right hp2Z (by omega)
    have i4 : p * (4 * Z) ≤ p * (4 * Z + b) := Nat.mul_le_mul_left p (by omega)
    linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [Nat.abundant_iff_sum_divisors, hsig, key]
    have : 0 < 2 * Z * (2 * j + 1) := by positivity
    linarith
  · -- not pseudoperfect
    rw [Nat.not_pseudoperfect_iff_forall]
    right
    intro s hs hsum
    have hsd := Finset.sum_sdiff hs (f := fun i => i)
    have hsp := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := Z * p * (4 * Z + b))
    rw [hsig, key] at hsp
    have hT : ∑ i ∈ (Z * p * (4 * Z + b)).properDivisors \ s, i =
        2 * Z * (2 * j + 1) + (b + 2 * j + 3) * (b + 1) := by
      linarith
    have hsmall : ∀ d ∈ (Z * p * (4 * Z + b)).properDivisors \ s, d < p * (4 * Z + b) := by
      intro d hd
      have := Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hd
      linarith
    have hsub : (Z * p * (4 * Z + b)).properDivisors \ s ⊆ (2 ^ k * p * (4 * Z + b)).divisors := by
      rw [hZ]
      exact Finset.sdiff_subset.trans Nat.properDivisors_subset_divisors
    obtain ⟨S0, B, C, hS0, hB, hC, hsum'⟩ := decomp k p (4 * Z + b) hp hq hpq _ hsub hsmall
    rw [hY] at hS0 hB hC
    rw [hT] at hsum'
    have hS0' : S0 + 1 ≤ 2 * Z := by omega
    by_cases hh : B + C ≤ j
    · have h1 : p * B + (4 * Z + b) * C ≤ (4 * Z + b) * j := by
        calc p * B + (4 * Z + b) * C ≤ (4 * Z + b) * B + (4 * Z + b) * C := by gcongr
          _ = (4 * Z + b) * (B + C) := by ring
          _ ≤ (4 * Z + b) * j := by gcongr
      have h3 : b * j ≤ b * (2 * j) := Nat.mul_le_mul_left b (by omega)
      nlinarith
    · have h1 : p * (j + 1) ≤ p * B + (4 * Z + b) * C := by
        calc p * (j + 1) ≤ p * (B + C) := Nat.mul_le_mul_left p (by omega)
          _ = p * B + p * C := by ring
          _ ≤ p * B + (4 * Z + b) * C := by gcongr
      have hm : (p + (b + 2 * j + 4)) * (j + 1) = 4 * Z * (j + 1) := by rw [hpa]
      nlinarith
  · -- primitive
    intro d hd hw
    have hab_d := hw.1
    have hn0 : Z * p * (4 * Z + b) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by omega) hp.ne_zero) hq.ne_zero
    obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.1 hd
    obtain ⟨c, hc⟩ := hdn
    have hc1 : c ≠ 1 := by intro h; rw [h, mul_one] at hc; omega
    obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd hc1
    have hdr : d * r ∣ Z * p * (4 * Z + b) := by rw [hc]; exact Nat.mul_dvd_mul_left d hrc
    have hrn : r ∣ Z * p * (4 * Z + b) := Dvd.dvd.trans (Dvd.intro_left d rfl) hdr
    rcases (Nat.Prime.dvd_mul hr).1 hrn with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · -- r = 2
        rw [← hZ] at h
        have hr2 : r = 2 :=
          (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
        subst hr2
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
          rcases k with _ | k'
          · simp at h
          · exact ⟨k', rfl⟩
        obtain ⟨W, hWd⟩ : ∃ W, 2 ^ k' = W := ⟨_, rfl⟩
        have hZW : Z = 2 * W := by rw [← hZ, pow_succ, hWd]; ring
        have hW1 : 1 ≤ W := by omega
        have hdr' : d * 2 ∣ 2 * (W * p * (4 * Z + b)) := by
          have e : Z * p * (4 * Z + b) = 2 * (W * p * (4 * Z + b)) := by rw [hZW]; ring
          rwa [e] at hdr
        rw [mul_comm d 2] at hdr'
        have hdW : d ∣ W * p * (4 * Z + b) := Nat.dvd_of_mul_dvd_mul_left two_pos hdr'
        have habW := Nat.Abundant.of_dvd hab_d hdW
          (mul_ne_zero (mul_ne_zero (by omega) hp.ne_zero) hq.ne_zero)
        have hs3 := sigma_three k' hp hq hp2 hq2 hpq
        rw [hZ, hWd] at hs3
        rw [Nat.abundant_iff_sum_divisors, hs3] at habW
        zify [hZ1] at habW
        have hZW' : (Z : ℤ) = 2 * W := by exact_mod_cast hZW
        rw [hZW'] at habW
        have hpz : (p : ℤ) + (b + 2 * j + 4) = 8 * W := by omega
        have hp4 : (4 * W : ℤ) < p := by omega
        have i1 : ((2 : ℤ) * W - 1) * (p + (4 * (2 * W) + b) + 1) ≤ (2 * W - 1) * (16 * W) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have i2 : (4 * W : ℤ) * (8 * W) < p * (4 * (2 * W) + b) := by nlinarith
        nlinarith
      · -- r = p
        have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 h
        rw [hrp] at hdr
        have hdq : d ∣ Z * (4 * Z + b) := by
          rw [show Z * p * (4 * Z + b) = p * (Z * (4 * Z + b)) by ring, mul_comm d p] at hdr
          exact Nat.dvd_of_mul_dvd_mul_left hp.pos hdr
        have habq := Nat.Abundant.of_dvd hab_d hdq (mul_ne_zero (by omega) hq.ne_zero)
        have := not_abundant_two k hq hq2 (by rw [hY]; omega)
        rw [hZ] at this
        exact this habq
    · -- r = q
      have hrq : r = 4 * Z + b := (Nat.prime_dvd_prime_iff_eq hr hq).1 h
      rw [hrq] at hdr
      have hdp : d ∣ Z * p := by
        rw [mul_comm d] at hdr
        exact Nat.dvd_of_mul_dvd_mul_left hq.pos (by rwa [mul_comm (Z * p)] at hdr)
      have habp := Nat.Abundant.of_dvd hab_d hdp (mul_ne_zero (by omega) hp.ne_zero)
      have := not_abundant_two k hp hp2 (by rw [hY]; omega)
      rw [hZ] at this
      exact this habp

end OMA.Erdos470H1Proof

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 :=
  OMA.Erdos470H1Proof.melfi
