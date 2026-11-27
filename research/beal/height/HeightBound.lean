import Mathlib.Data.Nat.Factorization.Basic

namespace BealHeight

/-- Product of the distinct prime divisors of n. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem rad_le_self {n : ℕ} (hn : 0 < n) : rad n ≤ n :=
  Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- Clear denominators in the reciprocal-sum bound. At least one exponent is
at least four, so the corresponding base contributes at most three twelfths
of the height. Each of the others contributes at most four twelfths. -/
theorem radical_gap {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (large : 4 ≤ x ∨ 4 ≤ y ∨ 4 ≤ z) (he : a^x + b^y = c^z) :
    rad (a*b*c)^12 < (c^z)^11 := by
  let H := c^z
  have hp : 0 < H := Nat.pow_pos hc
  have haH : a^x < H := by
    have := Nat.pow_pos (n := y) hb
    dsimp [H]; omega
  have hbH : b^y < H := by
    have := Nat.pow_pos (n := x) ha
    dsimp [H]; omega
  have pw {u v n : ℕ} (h : u < v) (hn : 0 < n) : u^n < v^n :=
    Nat.pow_lt_pow_left h hn.ne'
  have lebase {u m d : ℕ} (h : 0 < u) (hd : d ≤ m) : u^d ≤ u^m :=
    Nat.pow_le_pow_right h hd
  have common {u m d : ℕ} (h : 0 < u) (hd : d ≤ m) (hu : u^m < H) (r : ℕ)
      (hr : 0 < r) : u^(d*r) < H^r := by
    rw [Nat.pow_mul]
    exact pw ((lebase h hd).trans_lt hu) hr
  have bnd {d : ℕ} (hd : d ≤ z) (r : ℕ) : c^(d*r) ≤ H^r := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (lebase hc hd) r
  have prod {i j k : ℕ} (hi : a^12 < H^i) (hj : b^12 < H^j)
      (hk : c^12 ≤ H^k) : (a*b*c)^12 < H^(i+j+k) := by
    rw [Nat.mul_pow, Nat.mul_pow, Nat.pow_add, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hi (Nat.le_of_lt hj) (Nat.pow_pos hp)) hk (Nat.pow_pos hp)
  have h : (a*b*c)^12 < H^11 := by
    rcases large with h | h | h
    · exact prod (i:=3) (j:=4) (k:=4) (common ha h haH 3 (by decide))
        (common hb hy hbH 4 (by decide)) (bnd hz 4)
    · exact prod (i:=4) (j:=3) (k:=4) (common ha hx haH 4 (by decide))
        (common hb h hbH 3 (by decide)) (bnd hz 4)
    · exact prod (i:=4) (j:=4) (k:=3) (common ha hx haH 4 (by decide))
        (common hb hy hbH 4 (by decide)) (bnd h 3)
  exact (Nat.pow_le_pow_left (rad_le_self (Nat.mul_pos (Nat.mul_pos ha hb) hc)) 12).trans_lt h

/-- The integer form of H ≤ K R^(23/22), together with the radical gap,
gives the explicit height cutoff H < K^24. -/
theorem cutoff {H R K : ℕ} (hp : 0 < H) (gap : R^12 < H^11)
    (estimate : H^22 ≤ K^22 * R^23) : H < K^24 := by
  have hk : 0 < K := by
    by_contra! hn
    have hz : K = 0 := by omega
    rw [hz] at estimate
    simp at estimate
    omega
  have g := Nat.pow_lt_pow_left gap (n := 23) (by decide)
  have e := Nat.pow_le_pow_left estimate 12
  rw [Nat.mul_pow] at e
  have per : (R^23)^12 = (R^12)^23 := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm 23 12]
  rw [per] at e
  have q := e.trans_lt (Nat.mul_lt_mul_of_pos_left g (Nat.pow_pos (Nat.pow_pos hk)))
  have left : (H^22)^12 = H^11 * H^253 := by rw [← Nat.pow_mul, ← Nat.pow_add]
  have right : (K^22)^12 * (H^11)^23 = (K^24)^11 * H^253 := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul]
  rw [left, right] at q
  have lt := Nat.lt_of_mul_lt_mul_right q
  exact Nat.lt_of_not_ge fun h => (Nat.not_lt_of_ge (Nat.pow_le_pow_left h 11)) lt

end BealHeight

#print axioms BealHeight.radical_gap
#print axioms BealHeight.cutoff
