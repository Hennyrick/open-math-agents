import OMAStatements.S_oeis_a216971
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset

/-!
# Divisibility of every row of OEIS A216971

The number of maps with a prescribed periodic set of size r and a fixed
entry count is independent of the labels. Swapping periodic targets shows
that this number is divisible by r. Summing over the sets of size r gives
a multiple of n, since r times n choose r equals n times n−1 choose r−1.

Source: https://oeis.org/A216971
Credit: @Hennyrick
-/

namespace OMA.FunctionCycles
open Function

/-- A finite nonempty endofunction has a cyclic vertex. -/
theorem periodicPts_nonempty {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    (periodicPts f).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨m, n, h, hne⟩ : ∃ m n : ℕ, f^[m] x = f^[n] x ∧ m ≠ n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  have aux {i j : ℕ} (hij : i < j) (he : f^[i] x = f^[j] x) : (periodicPts f).Nonempty := by
    refine ⟨f^[i] x, j-i, by omega, ?_⟩
    change f^[j-i] (f^[i] x) = f^[i] x
    simpa only [← iterate_add_apply, Nat.sub_add_cancel hij.le] using he.symm
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact aux hl h
  · exact aux hl h.symm

theorem periodicPts_eq_of_change {α : Type*} [Finite α] (f g : α → α)
    (maps : Set.MapsTo g (periodicPts f) (periodicPts f))
    (inj : Set.InjOn g (periodicPts f))
    (off : ∀ x, x ∉ periodicPts f → g x = f x) : periodicPts g = periodicPts f := by
  have outside (k : ℕ) (x : α) (h : g^[k] x ∉ periodicPts f) : g^[k] x = f^[k] x := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at *
      have prior : g^[k] x ∉ periodicPts f := fun hx => h (maps hx)
      rw [off _ prior, ih prior]
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    obtain ⟨k, hk, hfix⟩ := hx
    have hg : g^[k] x = x := hfix.eq
    exact hn ⟨k, hk, (outside k x (by simpa only [hg] using hn)).symm.trans hg⟩
  · intro x hx
    let G : periodicPts f → periodicPts f := fun y => ⟨g y, maps y.property⟩
    have hG : Injective G := fun y z h => Subtype.ext (inj y.property z.property (congrArg Subtype.val h))
    have hsc : Semiconj (fun y : periodicPts f => (y : α)) G g := fun _ => rfl
    exact hsc.mapsTo_periodicPts (hG.mem_periodicPts ⟨x,hx⟩)

theorem entrySet_eq_of_change {α : Type*} (f g : α → α)
    (hR : periodicPts g = periodicPts f) (off : ∀ x, x ∉ periodicPts f → g x = f x) :
    {x | x ∉ periodicPts g ∧ g x ∈ periodicPts g} = {x | x ∉ periodicPts f ∧ f x ∈ periodicPts f} := by
  rw [hR]
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr_right (fun hx => by rw [off x hx])

end OMA.FunctionCycles

namespace OMA.FunctionCycles
open Function
open scoped Classical

/-- Swap two periodic targets on edges whose source is itself periodic. -/
private def swapTargets {n : ℕ} (R : Finset (Fin n)) (y z : Fin n) (f : Fin n → Fin n)
    (x : Fin n) : Fin n := if x ∈ R then Equiv.swap y z (f x) else f x

private theorem fiber_change {n k : ℕ} {R : Finset (Fin n)} {y z : Fin n}
    (hy : y ∈ R) (hz : z ∈ R) (f : Fin n → Fin n)
    (hR : (periodicPts f).toFinset = R)
    (hc : {x : Fin n | x ∉ periodicPts f ∧ f x ∈ periodicPts f}.ncard = k) :
    (periodicPts (swapTargets R y z f)).toFinset = R ∧
    {x : Fin n | x ∉ periodicPts (swapTargets R y z f) ∧
      swapTargets R y z f x ∈ periodicPts (swapTargets R y z f)}.ncard = k := by
  classical
  let g := swapTargets R y z f
  have mem (x : Fin n) : x ∈ periodicPts f ↔ x ∈ R := by rw [← hR]; simp
  have off : ∀ x, x ∉ periodicPts f → g x = f x := by
    intro x hx
    have hn : x ∉ R := fun e => hx ((mem x).mpr e)
    simp [g, swapTargets, hn]
  have permR : periodicPts g = periodicPts f := by
    apply periodicPts_eq_of_change f g _ _ off
    · intro x hx
      rw [mem]
      have hr := (mem x).mp hx
      have hf := (mem (f x)).mp ((bijOn_periodicPts f).mapsTo hx)
      simp only [g, swapTargets, if_pos hr]
      by_cases ey : f x = y
      · simpa [ey] using hz
      by_cases ez : f x = z
      · simpa [ez] using hy
      simpa only [Equiv.swap_apply_of_ne_of_ne ey ez] using hf
    · intro x hx x' hx' eq
      simp only [g, swapTargets, if_pos ((mem x).mp hx), if_pos ((mem x').mp hx')] at eq
      exact (bijOn_periodicPts f).injOn hx hx' ((Equiv.swap y z).injective eq)
  exact ⟨by change (periodicPts g).toFinset = R; rwa [permR],
    (congrArg Set.ncard (entrySet_eq_of_change f g permR off)).trans hc⟩

/-- For a fixed nonempty recurrent set, its size divides the number of maps with a prescribed
number of entries into that set. Swapping the targets of recurrent edges identifies the fibres
of the map that records the image of a chosen recurrent vertex. -/
theorem fiber_dvd {n k : ℕ} (R : Finset (Fin n)) (hr : R.Nonempty) :
    R.card ∣ Nat.card {f : Fin n → Fin n // (periodicPts f).toFinset = R ∧
      {x : Fin n | x ∉ periodicPts f ∧ f x ∈ periodicPts f}.ncard = k} := by
  classical
  let E := {f : Fin n → Fin n // (periodicPts f).toFinset = R ∧
    {x : Fin n | x ∉ periodicPts f ∧ f x ∈ periodicPts f}.ncard = k}
  obtain ⟨v,hv⟩ := hr
  let base : R := ⟨v,hv⟩
  let mark (f : E) : R := ⟨f.val v, by
    have hv' : v ∈ periodicPts f.val := by simpa [← f.property.1] using hv
    have h' := (bijOn_periodicPts f.val).mapsTo hv'
    simpa [← f.property.1] using h'⟩
  let twist (y : R) (f : E) : E := ⟨swapTargets R y v f.val,
    fiber_change y.property hv f.val f.property.1 f.property.2⟩
  have twice (y : R) (f : E) : twist y (twist y f) = f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ R <;> simp [twist, swapTargets, hx]
  have images (y : R) (f : E) : (mark (twist y f) : Fin n) = Equiv.swap (y : Fin n) v (mark f) := by
    simp [mark, twist, swapTargets, hv]
  let matching (y : R) : {f : E // mark f = y} ≃ {f : E // mark f = base} :=
    { toFun := fun f => ⟨twist y f.val, Subtype.ext (by rw [images, f.property]; exact Equiv.swap_apply_left _ _)⟩
      invFun := fun f => ⟨twist y f.val, Subtype.ext (by rw [images, f.property]; exact Equiv.swap_apply_right _ _)⟩
      left_inv := fun f => Subtype.ext (twice _ _)
      right_inv := fun f => Subtype.ext (twice _ _) }
  let e := (Equiv.sigmaFiberEquiv mark).symm.trans (Equiv.sigmaEquivProdOfEquiv matching)
  refine ⟨Nat.card {f : E // mark f = base}, ?_⟩
  change Nat.card E = _
  rw [Nat.card_congr e, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

end OMA.FunctionCycles

namespace OMA.FunctionCycles

open Function
open scoped Classical

private theorem perm_of_equal_card {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ e : Equiv.Perm (Fin n), ∀ x, e x ∈ T ↔ x ∈ S := by
  classical
  have hc : Fintype.card {x : Fin n // x ∈ S} = Fintype.card {x : Fin n // x ∈ T} := by simpa using h
  let inside := Fintype.equivOfCardEq hc
  let outside := Fintype.equivOfCardEq (Fintype.card_compl_eq_card_compl (· ∈ S) (· ∈ T) hc)
  let e := ((Equiv.sumCompl (· ∈ S)).symm.trans (Equiv.sumCongr inside outside)).trans (Equiv.sumCompl (· ∈ T))
  refine ⟨e, fun x => ?_⟩
  by_cases hx : x ∈ S
  · have he : e x = (inside ⟨x,hx⟩).val := by simp [e, Equiv.sumCompl_symm_apply_of_pos hx]
    simp [he,(inside ⟨x,hx⟩).property,hx]
  · have he : e x = (outside ⟨x,hx⟩).val := by simp [e, Equiv.sumCompl_symm_apply_of_neg hx]
    simp [he,(outside ⟨x,hx⟩).property,hx]

private theorem permutes_cycles {α : Type*} (e : Equiv.Perm α) (f : α → α) (x : α) :
    e x ∈ periodicPts (e.arrowCongr e f) ↔ x ∈ periodicPts f := by
  have forward : Semiconj e f (e.arrowCongr e f) := fun x => by simp [Equiv.arrowCongr]
  have back : Semiconj e.symm (e.arrowCongr e f) f := fun x => by simp [Equiv.arrowCongr]
  constructor
  · intro hx
    simpa using back.mapsTo_periodicPts hx
  · exact fun hx => forward.mapsTo_periodicPts hx

private theorem permutes_entry_count {n : ℕ} (e : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    {y : Fin n | y ∉ periodicPts (e.arrowCongr e f) ∧ (e.arrowCongr e f) y ∈ periodicPts (e.arrowCongr e f)}.ncard =
      {x : Fin n | x ∉ periodicPts f ∧ f x ∈ periodicPts f}.ncard := by
  let A : Set (Fin n) := {x | x ∉ periodicPts f ∧ f x ∈ periodicPts f}
  have he : e '' A = {y : Fin n | y ∉ periodicPts (e.arrowCongr e f) ∧ (e.arrowCongr e f) y ∈ periodicPts (e.arrowCongr e f)} := by
    ext y
    obtain ⟨x,rfl⟩ := e.surjective y
    simp [A, Equiv.arrowCongr_apply, permutes_cycles]
  rw [← he]
  exact Set.ncard_image_of_injective _ e.injective

theorem same_fiber_card {n k : ℕ} (S T : Finset (Fin n)) (hc : S.card = T.card) :
    Nat.card {f : Fin n → Fin n // (periodicPts f).toFinset = S ∧
      {x : Fin n | x ∉ periodicPts f ∧ f x ∈ periodicPts f}.ncard = k} =
    Nat.card {g : Fin n → Fin n // (periodicPts g).toFinset = T ∧
      {x : Fin n | x ∉ periodicPts g ∧ g x ∈ periodicPts g}.ncard = k} := by
  classical
  obtain ⟨e,he⟩ := perm_of_equal_card S T hc
  apply Nat.card_congr
  apply (e.arrowCongr e).subtypeEquiv
  intro f
  have hST : (periodicPts f).toFinset = S ↔ (periodicPts (e.arrowCongr e f)).toFinset = T := by
    constructor
    · intro h
      ext y
      obtain ⟨x,rfl⟩ := e.surjective y
      simp [he, ← h, permutes_cycles]
    · intro h
      ext x
      simpa only [Set.mem_toFinset, permutes_cycles, he] using (Finset.ext_iff.mp h (e x))
  exact and_congr hST (by rw [permutes_entry_count])

end OMA.FunctionCycles

namespace OMA.A216971

open Finset

/-- If all fibres over r-element label sets have the same cardinality divisible by r,
then the number of objects is divisible by the number of labels. -/
theorem count_dvd {n : ℕ} {X : Type*} (E : Finset X) (R : X → Finset (Fin n))
    (hsame : ∀ S T : Finset (Fin n), S.card = T.card →
      (E.filter (fun x => R x = S)).card = (E.filter (fun x => R x = T)).card)
    (hdiv : ∀ S : Finset (Fin n), S.card ∣ (E.filter (fun x => R x = S)).card) :
    n ∣ E.card := by
  classical
  let U := (univ : Finset (Fin n))
  let c := fun S : Finset (Fin n) => (E.filter (fun x => R x = S)).card
  have split : E.card = ∑ S ∈ U.powerset, c S :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
  rw [split, Finset.sum_powerset]
  apply Finset.dvd_sum
  intro r _
  by_cases ex : (U.powersetCard r).Nonempty
  · obtain ⟨S, hS⟩ := ex
    have hSr := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨m, hm⟩ := hdiv S
    have hh : ∑ T ∈ U.powersetCard r, c T = n.choose r * c S := by
      calc
        _ = ∑ _T ∈ U.powersetCard r, c S := Finset.sum_congr rfl (fun T hT =>
          hsame T S (((Finset.mem_powersetCard.mp hT).2).trans hSr.symm))
        _ = _ := by simp [U, Finset.card_powersetCard]
    rw [hh]
    change c S = S.card*m at hm
    rw [hm,hSr,← Nat.mul_assoc]
    apply dvd_mul_of_dvd_left
    cases r with
    | zero => simp
    | succ r =>
      have h := Nat.choose_mul (n := n) (k := r + 1) (s := 1) (by omega)
      simp only [Nat.choose_one_right] at h
      rw [h]
      exact dvd_mul_right _ _
  · simp [Finset.not_nonempty_iff_eq_empty.mp ex]

/-- The zero-size fibre vanishes when every object has a nonempty set of labels. -/
theorem count_dvd_ncard {n : ℕ} {X : Type*} [Fintype X]
    (P : X → Prop) (R : X → Finset (Fin n)) (hne : ∀ x, (R x).Nonempty)
    (hsame : ∀ S T : Finset (Fin n), S.card = T.card →
      Nat.card {x : X // R x = S ∧ P x} = Nat.card {x : X // R x = T ∧ P x})
    (hdiv : ∀ S : Finset (Fin n), S.Nonempty → S.card ∣ Nat.card {x : X // R x = S ∧ P x}) :
    n ∣ {x : X | P x}.ncard := by
  classical
  let E := (univ : Finset X).filter P
  have total : {x : X | P x}.ncard = E.card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [E]
  have fibre (S : Finset (Fin n)) :
      (E.filter (fun x => R x = S)).card = Nat.card {x : X // R x = S ∧ P x} := by
    change _ = {x : X | R x = S ∧ P x}.ncard
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [E, and_comm]
  rw [total]
  apply count_dvd E R
  · intro S T h
    rw [fibre, fibre, hsame S T h]
  · intro S
    by_cases hs : S.Nonempty
    · rw [fibre]
      exact hdiv S hs
    · have hempty : E.filter (fun x => R x = S) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have h := (Finset.mem_filter.mp hx).2
        exact hs (h ▸ hne x)
      rw [hempty, Finset.card_empty]
      exact dvd_zero _

end OMA.A216971

theorem OMA.solution : type_of% @OMA.S_oeis_a216971.main := by
  classical
  intro n k hn _hk
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply OMA.A216971.count_dvd_ncard
    (fun f : Fin n → Fin n => {x : Fin n | x ∉ Function.periodicPts f ∧ f x ∈ Function.periodicPts f}.ncard = k)
    (fun f => (Function.periodicPts f).toFinset)
  · intro f
    exact Set.toFinset_nonempty.mpr (OMA.FunctionCycles.periodicPts_nonempty f)
  · exact OMA.FunctionCycles.same_fiber_card
  · exact OMA.FunctionCycles.fiber_dvd
