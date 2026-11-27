import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Ring

namespace BealCartanScalar

/-- A conjugate pair with trace d(1+q) and norm q has repeated root d
when both q and d are fixed and d²=1. In particular q=1. -/
theorem fixed_trace_norm {L : Type*} [Field L] (σ : L ≃+* L) {z q d : L}
    (hq : σ q = q) (hd : σ d = d) (hs : d ^ 2 = 1)
    (ht : z + σ z = d * (1 + q)) (hn : z * σ z = q) :
    q = 1 := by
  have roots : (z - d) * (z - d*q) = 0 := by
    calc
      _ = z^2 - z*(d*(1+q)) + d^2*q := by ring
      _ = z^2 - z*(z+σ z) + 1*q := by rw [← ht, hs]
      _ = q - z*(σ z) := by ring
      _ = 0 := by rw [hn, sub_self]
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hs
  have zero : d * (q-1) = 0 := by
    rcases mul_eq_zero.mp roots with h | h
    · rw [sub_eq_zero.mp h, hd] at ht
      calc
        _ = d*(1+q) - (d+d) := by ring
        _ = 0 := by rw [← ht, sub_self]
    · rw [sub_eq_zero.mp h, map_mul, hd, hq] at ht
      calc
        _ = (d*q+d*q) - d*(1+q) := by ring
        _ = 0 := by rw [ht, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left hd0)

/-- Precomposing a character with a surjective map preserves and detects
triviality. In particular this applies to conjugation on an inertia group. -/
theorem trivial_after_surjection_iff {A B G : Type*} [One G]
    (F : A → B) (hF : Function.Surjective F) (τ : B → G) :
    (∀ a, τ (F a) = 1) ↔ (∀ b, τ b = 1) := by
  constructor
  · intro h b
    obtain ⟨a, rfl⟩ := hF b
    exact h a
  · intro h a
    exact h (F a)

end BealCartanScalar
