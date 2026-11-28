import Erdos142ParityCarry
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

namespace ParityMass
open DigitProof Finset

private def leftBit (z : Fin 3) (u : Bool) : Bool :=
  if z=0 then false else if z=1 then u else true
private def label (z : Fin 3) (u : Bool) : Fin 3 :=
  if z=1 then 2 else if u then 1 else 0
private def bitNat (u : Bool) : ℕ := if u then 1 else 0

private theorem digit_sum (z : Fin 3) (u : Bool) :
    bitNat (leftBit z u) + bitNat (leftBit z (!u)) = z.val := by decide +revert

private theorem recover (z w : Fin 3) (u v : Bool) :
    leftBit z u = leftBit w v → label z u = label w v → z=w ∧ u=v := by decide +revert

abbrev Trit (m : ℕ) := Fin m → Fin 3
abbrev Bit (m : ℕ) := Fin m → Bool

def valT {m} (z : Trit m) := ∑ i, (z i).val * 3^i.val
def valB {m} (p : Bit m) := ∑ i, bitNat (p i) * 3^i.val

private def endpoint {m} (z : Trit m) (u : Bit m) : Bit m := fun i => leftBit (z i) (u i)
private def tag {m} (z : Trit m) (u : Bit m) : Trit m := fun i => label (z i) (u i)
private def flip {m} (u : Bit m) : Bit m := fun i => !(u i)

private theorem sum_eq {m} (z : Trit m) (u : Bit m) :
    valB (endpoint z u) + valB (endpoint z (flip u)) = valT z := by
  unfold valB valT
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← Nat.add_mul]
  exact congrArg (fun n => n*3^i.val) (digit_sum (z i) (u i))

private theorem code_inj {m} {z w : Trit m} {u v : Bit m}
    (h : endpoint z u = endpoint w v) (hh : tag z u = tag w v) : z=w ∧ u=v := by
  have atDigit (i : Fin m) := recover (z i) (w i) (u i) (v i) (congrFun h i) (congrFun hh i)
  exact ⟨funext fun i => (atDigit i).1, funext fun i => (atDigit i).2⟩

/-- H is any collection of occupied ternary sites outside the doubled
Cantor set. D is any collection containing the deleted binary-digit words.
The inequality applies to all 3-AP-free A, with no algorithmic restriction. -/
theorem mass_bound {m : ℕ} (A : ℕ → Prop) (hf : APFree 3 A)
    (H : Finset (Trit m)) (D : Finset (Bit m))
    (occupied : ∀ z ∈ H, A (valT z))
    (outside : ∀ z ∈ H, ∀ u : Bit m, valT z ≠ 2*valB u)
    (deleted : ∀ u : Bit m, ¬ A (2*valB u) → u∈D) :
    H.card * 2^m ≤ 2 * (D.card * 3^m) := by
  classical
  have hit (z : H) (u : Bit m) :
      endpoint z.val u ∈ D ∨ endpoint z.val (flip u) ∈ D := by
    by_contra! avoid
    let x := valB (endpoint z.val u)
    let y := valB (endpoint z.val (flip u))
    have hx : A (2*x) := by by_contra h; exact avoid.1 (deleted _ h)
    have hy : A (2*y) := by by_contra h; exact avoid.2 (deleted _ h)
    have he : x+y=valT z.val := sum_eq z.val u
    have ne := outside z.val z.property (endpoint z.val u)
    have ht := occupied z.val z.property
    let a := min x y
    let b := max x y
    have hsum : a+b=valT z.val := by dsimp [a,b]; omega
    have hlt : a<b := by dsimp [a,b]; omega
    have ends : A (2*a) ∧ A (2*b) := by
      by_cases c : x≤y
      · simpa [a,b,min_eq_left c,max_eq_right c] using And.intro hx hy
      · have c' : y≤x := by omega
        simpa [a,b,min_eq_right c',max_eq_left c'] using And.intro hy hx
    apply hf (2*a) (b-a) (by omega)
    intro i hi
    have : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases this with rfl|rfl|rfl
    · simpa using ends.1
    · rw [show 2*a+1*(b-a)=valT z.val by omega]; exact ht
    · rw [show 2*a+2*(b-a)=2*b by omega]; exact ends.2
  let put (p : H × Bit m) : (D × Trit m) ⊕ (D × Trit m) :=
    if h : endpoint p.1.val p.2 ∈ D then
      Sum.inl (⟨_,h⟩,tag p.1.val p.2)
    else Sum.inr (⟨_,(hit p.1 p.2).resolve_left h⟩,tag p.1.val (flip p.2))
  have inj : Function.Injective put := by
    rintro ⟨z,u⟩ ⟨w,v⟩ h
    dsimp only [put] at h
    split at h <;> split at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, Subtype.mk.injEq, reduceCtorEq] at h
    · obtain ⟨hz,hu⟩ := code_inj h.1 h.2
      exact Prod.ext (Subtype.ext hz) hu
    · obtain ⟨hz,hu⟩ := code_inj h.1 h.2
      apply Prod.ext (Subtype.ext hz)
      funext i
      simpa [flip] using congrArg Bool.not (congrFun hu i)
  have := Fintype.card_le_of_injective put inj
  simpa [Trit,Bit,two_mul] using this


/-- Encode a doubled {0,1}-digit integer as a ternary integer with digits 0 or 2. -/
def doubled {m} (p : Bit m) : Fin (3^m) :=
  finFunctionFinEquiv (fun i : Fin m => if p i then (2 : Fin 3) else 0)

private theorem doubled_value {m} (p : Bit m) : (doubled p).val = 2*valB p := by
  rw [doubled,finFunctionFinEquiv_apply,valB,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  cases p i <;> simp [bitNat]

private theorem doubled_inj (m : ℕ) : Function.Injective (@doubled m) := by
  intro a b eq
  have he := finFunctionFinEquiv.injective eq
  funext i
  have v := congrFun he i
  cases ha : a i <;> cases hb : b i <;> simp_all

def core (m : ℕ) : Finset (Fin (3^m)) := univ.image doubled

theorem core_card (m : ℕ) : (core m).card = 2^m := by
  simp [core,card_image_of_injective _ (doubled_inj m),Bit]

/-- Quantitative stability inequality directly on the integer interval [0,3^m).
Points outside the canonical core are paid for by missing core points. -/
theorem integer_stability {m : ℕ} (A : Finset (Fin (3^m)))
    (hf : APFree 3 (fun x => x ∈ A.image Fin.val)) :
    (A \ core m).card * 2^m ≤ 2 * ((core m \ A).card * 3^m) := by
  classical
  let e : Trit m ≃ Fin (3^m) := finFunctionFinEquiv
  let H := (A \ core m).map e.symm.toEmbedding
  let D : Finset (Bit m) := univ.filter fun p => doubled p ∉ A
  have spec (z : Trit m) : z ∈ H ↔ e z ∈ A \ core m := by simp [H]
  have occ (z : Trit m) (hz : z ∈ H) : valT z ∈ A.image Fin.val := by
    exact mem_image.mpr ⟨e z,(mem_sdiff.mp ((spec z).mp hz)).1,finFunctionFinEquiv_apply z⟩
  have out (z : Trit m) (hz : z ∈ H) (u : Bit m) : valT z ≠ 2*valB u := by
    intro he
    have eq : e z = doubled u := Fin.ext ((finFunctionFinEquiv_apply z).trans (he.trans (doubled_value u).symm))
    exact (mem_sdiff.mp ((spec z).mp hz)).2 (mem_image.mpr ⟨u,mem_univ _,eq.symm⟩)
  have miss (u : Bit m) (hu : 2*valB u ∉ A.image Fin.val) : u ∈ D := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,fun h => hu (mem_image.mpr ⟨doubled u,h,doubled_value u⟩)⟩
  have hD : D.image doubled = core m \ A := by
    ext x
    simp only [D,core,mem_image,mem_filter,mem_univ,true_and,mem_sdiff]
    constructor
    · rintro ⟨u,hu,rfl⟩; exact ⟨⟨u,rfl⟩,hu⟩
    · rintro ⟨⟨u,rfl⟩,hu⟩; exact ⟨u,hu,rfl⟩
  have cardD : D.card = (core m \ A).card := by
    rw [← hD,card_image_of_injective _ (doubled_inj m)]
  simpa [H,cardD] using mass_bound _ hf H D occ out miss

end ParityMass
