import Erdos142FaceBridge

namespace SingleHole

/-- Binary digits, written in order of increasing ternary place. -/
def value : List Bool → ℤ
  | [] => 0
  | b :: xs => (if b then 1 else 0) + 3 * value xs

def sign (b : Bool) : ℤ := if b then -1 else 1

/-- The next g transitions change bit, then the following one repeats. -/
def firstRepeat (prev : Bool) : ℕ → List Bool → Prop
  | 0, b :: _ => b = prev
  | g+1, b :: xs => b ≠ prev ∧ firstRepeat b g xs
  | _, [] => False

private theorem step (p b : Bool) (l r t : ℤ) :
    (∃ c : Bool, 4 * (((if c then 1 else 0) + 3*l) -
      ((if b then 1 else 0) + 3*r)) = -sign p + 3*t) ↔
    (b≠p ∧ 4*(l-r) = -sign b + t) := by
  cases p <;> cases b <;> simp [sign,Bool.exists_bool] <;> omega

private theorem lastStep (p b c : Bool) (l r : ℤ)
    (h : 4 * (((if c then 1 else 0) + 3*l) - ((if b then 1 else 0) + 3*r))
         = -sign p + sign b) : p=b := by
  cases p <;> cases b <;> cases c <;> simp [sign] at * <;> omega

/-- The exact ternary carry rule for a possible core midpoint after a
single core deletion. The exponent g points to the right-hand changed
coordinate; the preceding bit is prev. -/
theorem carry_iff (prev : Bool) (g : ℕ) (xs : List Bool) (bound : g<xs.length) :
    (∃ ys : List Bool, ys.length=xs.length ∧
      4*(value ys-value xs) = -sign prev + sign xs[g]! * (3:ℤ)^g) ↔
    firstRepeat prev g xs := by
  induction g generalizing prev xs with
  | zero =>
    cases xs with
    | nil => simp at bound
    | cons b xs =>
      simp only [List.getElem!_cons_zero, pow_zero, mul_one,firstRepeat]
      constructor
      · rintro ⟨ys,hl,he⟩
        cases ys with
        | nil => simp at hl
        | cons c ys => exact (lastStep prev b c _ _ he).symm
      · rintro rfl
        exact ⟨b::xs,rfl,by ring⟩
  | succ g ih =>
    cases xs with
    | nil => simp at bound
    | cons b xs =>
      have bound' : g<xs.length := by simpa using bound
      let t := sign xs[g]! * (3:ℤ)^g
      have rhs : sign (b::xs)[g+1]! * (3:ℤ)^(g+1) = 3*t := by
        simp [t,pow_succ]; ring
      rw [rhs]
      constructor
      · rintro ⟨ys,hl,he⟩
        cases ys with
        | nil => simp at hl
        | cons c ys =>
          have h := (step prev b (value ys) (value xs) t).mp ⟨c,he⟩
          exact ⟨h.1,(ih b xs bound').mp ⟨ys,by simpa using hl,h.2⟩⟩
      · rintro ⟨ne,h⟩
        obtain ⟨ys,hl,he⟩ := (ih b xs bound').mpr h
        obtain ⟨c,hc⟩ := (step prev b (value ys) (value xs) t).mpr ⟨ne,he⟩
        exact ⟨c::ys,by simpa using hl,hc⟩

/-- delta is four times the change of binary-digit integer between words
of the same length. This is the integer midpoint test on the doubled core. -/
def represents (xs : List Bool) (delta : ℤ) :=
  ∃ ys : List Bool, ys.length=xs.length ∧ 4*(value ys-value xs)=delta

private theorem passDigit (b c : Bool) (l r t : ℤ)
    (h : 4 * (((if c then 1 else 0) + 3*l) - ((if b then 1 else 0) + 3*r))
         = 3*t) : 4*(l-r)=t := by
  cases b <;> cases c <;> simp at h <;> omega

private theorem pass (b : Bool) (xs : List Bool) (t : ℤ) :
    represents (b::xs) (3*t) ↔ represents xs t := by
  constructor
  · rintro ⟨ys,hl,he⟩
    cases ys with
    | nil => simp at hl
    | cons c ys => exact ⟨ys,by simpa using hl,passDigit b c _ _ _ he⟩
  · rintro ⟨ys,hl,he⟩
    exact ⟨b::ys,by simpa using hl,by unfold value; omega⟩

private theorem passPrefix (low xs : List Bool) (t : ℤ) :
    represents (low++xs) ((3:ℤ)^low.length * t) ↔ represents xs t := by
  induction low with
  | nil => simp
  | cons b low ih =>
    simpa only [List.cons_append,List.length_cons,pow_succ,
      show (3:ℤ)^low.length*3*t=3*(3^low.length*t) by ring] using
      (pass b (low++xs) ((3:ℤ)^low.length*t)).trans ih

private theorem firstDigit (b c : Bool) (l r t : ℤ)
    (h : 4 * (((if c then 1 else 0) + 3*l) - ((if b then 1 else 0) + 3*r))
         = sign b+3*t) : 4*(l-r) = -sign b+t := by
  cases b <;> cases c <;> simp [sign] at * <;> omega

private theorem start (b : Bool) (xs : List Bool) (t : ℤ) :
    represents (b::xs) (sign b+3*t) ↔ represents xs (-sign b+t) := by
  constructor
  · rintro ⟨ys,hl,he⟩
    cases ys with
    | nil => simp at hl
    | cons c ys => exact ⟨ys,by simpa using hl,firstDigit b c _ _ _ he⟩
  · rintro ⟨ys,hl,he⟩
    exact ⟨(!b)::ys,by simpa using hl,by cases b <;> simp [value,sign] at * <;> omega⟩

/-- For the edge midpoints indexed by i=low.length and j=i+g+1,
their ordinary integer midpoint belongs to the doubled core iff j is
the first repeated adjacent bit after i. The right side is read directly
from the missing word. -/
theorem pair_conflict_iff (low : List Bool) (b : Bool) (xs : List Bool) (g : ℕ)
    (bound : g<xs.length) :
    represents (low++b::xs) ((3:ℤ)^low.length * (sign b+3*(sign xs[g]! * 3^g))) ↔
      firstRepeat b g xs :=
  (passPrefix low (b::xs) _).trans ((start b xs _).trans (carry_iff b g xs bound))

end SingleHole
