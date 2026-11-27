import Std

namespace BealHeight

/-- The values of powers in the search, with their bases retained. -/
def powers (bound : Nat) : List (Nat × Nat) :=
  (if 1 ≤ bound then [(1, 1)] else []) ++
  (List.range (2 ^ (bound.log2 / 3 + 1))).flatMap fun a =>
    (List.range (bound.log2 + 1)).filterMap fun n =>
      if 2 ≤ a ∧ 3 ≤ n ∧ a ^ n ≤ bound then some (a, a ^ n) else none

theorem mem_powers {bound a v : Nat} :
    (a, v) ∈ powers bound ↔
      0 < a ∧ v ≤ bound ∧ ∃ n : Nat, 2 < n ∧ v = a ^ n := by
  unfold powers
  rw [List.mem_append]
  constructor
  · rintro (h | h)
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨by decide, by omega, 3, by decide, by decide⟩
      · simp at h
    · obtain ⟨b, _, h⟩ := List.mem_flatMap.mp h
      obtain ⟨n, _, h⟩ := List.mem_filterMap.mp h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by omega, by omega, n, by omega, rfl⟩
      · contradiction
  · rintro ⟨ha, hB, n, hn, rfl⟩
    by_cases h1 : a = 1
    · subst a
      left
      simp_all
    right
    have ha2 : 2 ≤ a := by omega
    have hpow := Nat.pow_pos ha (n := n)
    have hB0 : bound ≠ 0 := by omega
    have hnBound := (Nat.le_log2 hB0).mpr <| Nat.le_trans (Nat.pow_le_pow_left ha2 n) hB
    have haBound : a < 2 ^ (bound.log2 / 3 + 1) := by
      apply Nat.lt_of_not_ge
      intro hab
      have hc := Nat.le_trans (Nat.pow_le_pow_right ha (by omega : 3 ≤ n)) hB
      have h := Nat.le_trans (Nat.pow_le_pow_left hab 3) hc
      rw [← Nat.pow_mul] at h
      have := (Nat.le_log2 hB0).mpr h
      omega
    apply List.mem_flatMap.mpr
    refine ⟨a, List.mem_range.mpr haBound, List.mem_filterMap.mpr ?_⟩
    exact ⟨n, List.mem_range.mpr (by omega), by simp [ha2, hB, show 3 ≤ n by omega]⟩

/-- The bases for each power value. A value such as 64 has several bases. -/
def byValue : List (Nat × Nat) → Std.TreeMap Nat (List Nat)
  | [] => ∅
  | (a, v) :: rest =>
      let tail := byValue rest
      tail.insert v (a :: tail.getD v [])

theorem mem_byValue {xs : List (Nat × Nat)} {a v : Nat} :
    a ∈ (byValue xs).getD v [] ↔ (a, v) ∈ xs := by
  induction xs with
  | nil => simp [byValue]
  | cons t rest ih =>
    obtain ⟨u,w⟩ := t
    by_cases hw : w = v
    · subst w
      simp [byValue, Std.TreeMap.getD_insert_self, ih]
    · have hcmp : compare w v ≠ .eq := by simpa using hw
      simp [byValue, Std.TreeMap.getD_insert, hcmp, ih, Ne.symm hw]

/-- Check every pair of summands and every base for their sum. -/
def certifies (bound : Nat) : Bool :=
  let xs := powers bound
  let m := byValue xs
  xs.all fun a => xs.all fun b =>
    (m.getD (a.2 + b.2) []).all fun c => decide (1 < Nat.gcd a.1 (Nat.gcd b.1 c))

def HoldsUpTo (bound : Nat) : Prop :=
  ∀ {a b c x y z : Nat}, a ≠ 0 → b ≠ 0 → c ≠ 0 → 2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y = c ^ z → c ^ z ≤ bound → 1 < Nat.gcd a (Nat.gcd b c)

theorem certifies_iff (bound : Nat) : certifies bound = true ↔ HoldsUpTo bound := by
  unfold certifies HoldsUpTo
  simp only [List.all_eq_true, decide_eq_true_eq, mem_byValue]
  constructor
  · intro h a b c x y z ha hb hc hx hy hz he hbnd
    have hpos1 := Nat.pow_pos (Nat.pos_of_ne_zero ha) (n := x)
    have hpos2 := Nat.pow_pos (Nat.pos_of_ne_zero hb) (n := y)
    apply h (a,a^x) (mem_powers.mpr ⟨by omega, by omega, x, hx, rfl⟩)
      (b,b^y) (mem_powers.mpr ⟨by omega, by omega, y, hy, rfl⟩) c
    change (c, a^x + b^y) ∈ powers bound
    rw [he]
    exact mem_powers.mpr ⟨by omega, hbnd, z, hz, rfl⟩
  · intro h ⟨a,A⟩ hA ⟨b,B⟩ hB c hC
    obtain ⟨ha, _, x, hx, rfl⟩ := mem_powers.mp hA
    obtain ⟨hb, _, y, hy, rfl⟩ := mem_powers.mp hB
    obtain ⟨hc, hbound, z, hz, he⟩ := mem_powers.mp hC
    exact h (by omega) (by omega) (by omega) hx hy hz he (by simpa [← he] using hbound)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- A bounded Beal theorem verified by kernel reduction. -/
theorem holds_ten_thousand : HoldsUpTo 10000 :=
  (certifies_iff 10000).1 (by decide)

end BealHeight
