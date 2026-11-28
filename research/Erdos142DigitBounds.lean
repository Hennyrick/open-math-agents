import Std
import FormalConjecturesForMathlib.Combinatorics.AP.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Arithmetic-progression-free digit languages for Erdős problem 142

Research note for the Left to Solve isTheta team. Verified with Lean 4.33.1
and formal-conjectures 9097e2f90e66d2f6244209cb1c07f7120d17ec53.
The declarations concern restricted families; the unrestricted order is open.

## Exact maximum with two states

Read m ternary digits from left to right, with leading zeroes. The transition
may vary with the digit position, and the recogniser may vary with m. Among
such two-state recognisers whose accepted values avoid nonconstant 3-term
arithmetic progressions, the maximum number accepted is exactly 2^m.
See `ternary_two_state_exact`.

The digits {0,1} attain the bound. Modulo 3, three allowed digits satisfying
a+c=2b must all agree; stripping that digit proves progression-freeness.
For the upper bound the two-digit case checks the possible two-state tables.
For three or more digits, colour the first nine penultimate prefixes by their
state. Some three prefixes in arithmetic progression have the same colour,
by the finite two-colour case of van der Waerden's theorem, checked here.
Any accepted final digit from that colour would complete a forbidden triple.
Only the other state can accept a final digit. Its allowed suffix set has at
most two digits, and the prefixes reaching that state are progression-free
because any one allowed suffix embeds the prefixes into the full set.
Induction gives the matching upper bound.

## Arbitrary width and matrix rank

Write r_k(B) for the pinned maximum on [1,B]. For a deterministic recogniser
on t digits in base B with at most s states per layer, an AP-free language
has at most (s r_k(B))^t words, k >= 2. Hold a prefix and a reachable state
fixed at the end of a block. A single accepting suffix completes every
block in this fibre, so these blocks map affinely to an AP-free set.
See `machine_word_bound` and `pinned_extremalBound`.

For any field and cut matrix H, assign (i,j) the integer iB+j. If the
support avoids k-term progressions, its size is at most
rank(H) r_k(M) r_k(B), for dimensions M by B. Fixing either index embeds
the other affinely. Basis columns cover all nonzero rows.
See `pinned_rank_bound`.

## Consequence on paper (the analysis in this section is not formalised)

Fix a digit base b >= 2, N=b^n, and a constant K >= 1. Suppose a width-s
machine accepts a 3-AP-free set of size at least r_3(N)/K. Put B=b^L, q=floor(n/L). For each
initial prefix of n-qL digits, group the rest in q blocks. Dividing the
finite counting bound by N gives density at most (s r_3(B)/B)^q.
Behrend's construction gives density at least exp(-C sqrt(log N))/K.
Raghavan's upper bound gives r_3(B)/B <= exp(-c (log B)^(1/6)/log log B).
Write X=log N and y=log B. The inequalities imply
log s >= c y^(1/6)/log y - (C sqrt X + log K)/q.
Choose L so y is within O(log b) of a X^(3/5)/(log X)^(6/5)
for a sufficiently small fixed a>0. Then q is asymptotic to X/y.
The positive term has coefficient of order a^(1/6), the loss of order a.
Thus log s >= c' X^(1/10)/(log X)^(6/5) for all sufficiently large N=b^n.
This is a lower bound on recognition width; it supplies no matching upper
and lower estimates for the unrestricted r_3(N).

Raghavan, Improved Bounds for 3-Progressions: https://arxiv.org/abs/2603.27045
Elsholtz, Hunter, Proske and Sauermann, Improving Behrend's construction:
https://arxiv.org/abs/2406.12290
Problem: https://www.erdosproblems.com/142
-/

namespace DigitProof

/-- The set contains no progression with positive common difference and length k. -/
def APFree (k : Nat) (A : Nat → Prop) : Prop :=
  ∀ a d : Nat, 0 < d → (∀ i : Nat, i < k → A (a + i * d)) → False

/-- An upper bound for the size of every k-AP-free subset of [0,B). -/
def ExtremalBound (k B r : Nat) : Prop :=
  ∀ xs : List Nat, xs.Nodup → (∀ x ∈ xs, x < B) →
    APFree k (fun x => x ∈ xs) → xs.length ≤ r

/-- Appending a common suffix maps a block progression to a progression of
positive difference. The offset is arbitrary and the scale is positive. -/
theorem affine_preimage_free {k offset scale : Nat} {A S : Nat → Prop}
    (hA : APFree k A) (hpos : 0 < scale)
    (hmap : ∀ x, S x → A (offset + x * scale)) : APFree k S := by
  intro a d hd hall
  apply hA (offset + a * scale) (d * scale) (Nat.mul_pos hd hpos)
  intro i hi
  simpa only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc] using
    hmap (a + i * d) (hall i hi)

/-- Each block in this list takes a prefix to the same live state. A common
suffix therefore completes every such block to an accepted number. Here
`place` is the power of the base corresponding to the length of the suffix. -/
theorem liveFibre_length_le {k B r pre place suffix : Nat} {A : Nat → Prop}
    {State : Type} (afterBlock : Nat → State) (liveState : State)
    (blocks : List Nat) (hd : blocks.Nodup) (hb : ∀ x ∈ blocks, x < B)
    (hs : ∀ x ∈ blocks, afterBlock x = liveState)
    (hcompletion : ∀ x, x < B → afterBlock x = liveState →
      A ((pre * B + x) * place + suffix))
    (hpos : 0 < place) (hA : APFree k A) (hbound : ExtremalBound k B r) :
    blocks.length ≤ r := by
  apply hbound blocks hd hb
  apply affine_preimage_free (offset := pre * B * place + suffix)
    (scale := place) hA hpos
  intro x hx
  have hc := hcompletion x (hb x hx) (hs x hx)
  rwa [Nat.add_mul, Nat.add_right_comm] at hc

end DigitProof

namespace DigitProof

/-- A list of at most `m` outputs per input gives at most `inputs.length * m` outputs. -/
theorem length_flatMap_le {α β : Type _} (inputs : List α) (outputs : α → List β)
    (m : Nat) (hm : ∀ a ∈ inputs, (outputs a).length ≤ m) :
    (inputs.flatMap outputs).length ≤ inputs.length * m := by
  induction inputs with
  | nil => simp
  | cons a as ih =>
    have h₁ := hm a (List.mem_cons_self ..)
    have h₂ := ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add h₁ h₂

/-- Cover distinct children by `s` state fibres, each of size at most `r`. -/
theorem children_length_le_of_fibre_cover {α : Type _} {s r : Nat}
    {children : List α} (hd : children.Nodup) (fibre : Fin s → List α)
    (hcover : ∀ a ∈ children, ∃ j, a ∈ fibre j)
    (hsize : ∀ j, (fibre j).length ≤ r) : children.length ≤ s * r := by
  have hsub : children ⊆ (List.finRange s).flatMap fibre := by
    intro a ha
    obtain ⟨j, hj⟩ := hcover a ha
    exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j, hj⟩
  exact Nat.le_trans (hd.length_le_of_subset hsub) (by
    simpa using length_flatMap_le (List.finRange s) fibre r (fun j _ => hsize j))

/-- Follow the allowed digits at each prefix, in left-to-right reading order. -/
def Follows {α : Type _} (children : List α → List α) :
    List α → List α → Prop
  | _, [] => True
  | p, a :: tail => a ∈ children p ∧ Follows children (p ++ [a]) tail

/-- Enumerate all accepted suffixes of the specified length from a prefix. -/
def extensions {α : Type _} (children : List α → List α) :
    Nat → List α → List (List α)
  | 0, _ => [[]]
  | t + 1, p => (children p).flatMap fun a =>
      (extensions children t (p ++ [a])).map (a :: ·)

theorem follows_mem_extensions {α : Type _} {children : List α → List α}
    (p v : List α) (h : Follows children p v) :
    v ∈ extensions children v.length p := by
  induction v generalizing p with
  | nil => simp [extensions]
  | cons a tail ih =>
    obtain ⟨ha, htail⟩ := h
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨tail, ih _ htail, rfl⟩⟩

theorem extensions_length_le {α : Type _} {children : List α → List α} {M : Nat}
    (h : ∀ p, (children p).length ≤ M) (t : Nat) (p : List α) :
    (extensions children t p).length ≤ M ^ t := by
  induction t generalizing p with
  | zero => simp [extensions]
  | succ t ih =>
    have hflat := length_flatMap_le (children p)
      (fun a => (extensions children t (p ++ [a])).map (a :: ·))
      (M ^ t) (fun a _ => by simpa using ih (p ++ [a]))
    exact Nat.le_trans hflat (by
      simpa [Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (M ^ t) (h p))

/-- Cardinality of any distinct accepted words of length `t`. The child bound
    may be taken only on live prefixes by assigning no children to dead ones. -/
theorem accepted_words_length_le {α : Type _} {children : List α → List α}
    {M t : Nat} (p : List α) (words : List (List α)) (hd : words.Nodup)
    (hlive : ∀ p, (children p).length ≤ M)
    (hwords : ∀ v ∈ words, v.length = t ∧ Follows children p v) :
    words.length ≤ M ^ t := by
  apply Nat.le_trans (hd.length_le_of_subset (l₂ := extensions children t p) ?_)
    (extensions_length_le hlive t p)
  intro v hv
  obtain ⟨hlen, hf⟩ := hwords v hv
  simpa [hlen] using follows_mem_extensions p v hf

/-- Group each live digit by the deterministic state it reaches after its
    prefix. A bound on each such fibre at each prefix bounds the word count. -/
theorem accepted_words_length_le_of_state_fibres {α : Type _} {s r t : Nat}
    (children : List α → List α) (state : List α → α → Fin s)
    (p : List α) (words : List (List α)) (hd : words.Nodup)
    (hchildren : ∀ q, (children q).Nodup)
    (hfibre : ∀ q j, ((children q).filter (fun a => decide (state q a = j))).length ≤ r)
    (hwords : ∀ v ∈ words, v.length = t ∧ Follows children p v) :
    words.length ≤ (s * r) ^ t := by
  apply accepted_words_length_le p words hd _ hwords
  intro q
  refine children_length_le_of_fibre_cover (hchildren q)
    (fun j => (children q).filter (fun a => decide (state q a = j))) ?_ (hfibre q)
  intro a ha
  exact ⟨state q a, List.mem_filter.mpr ⟨ha, by simp⟩⟩

end DigitProof

namespace DigitProof

/-- Numbers represented by a prefix and suffix meeting at the same cut state. -/
def rectangleValues (B : Nat) (prefixes suffixes : List Nat) : List Nat :=
  prefixes.flatMap fun p => suffixes.map (fun z => p * B + z)

theorem rectangleValues_length (B : Nat) (prefixes suffixes : List Nat) :
    (rectangleValues B prefixes suffixes).length = prefixes.length * suffixes.length := by
  induction prefixes with
  | nil => simp [rectangleValues]
  | cons p ps ih =>
    simp [rectangleValues, Nat.succ_mul, Nat.add_comm] at ih ⊢

/-- Fixing one suffix embeds all prefixes into the accepted set. Fixing one
prefix embeds all suffixes. Thus both sides of any nonempty accepting rectangle
are progression-free on their respective intervals. -/
theorem rectangle_card_le {k M B rM rB : Nat} {A : Nat → Prop}
    (hB : 0 < B) (hA : APFree k A)
    (hMbound : ExtremalBound k M rM) (hBbound : ExtremalBound k B rB)
    (prefixes suffixes : List Nat)
    (hdp : prefixes.Nodup) (hds : suffixes.Nodup)
    (hp : ∀ p ∈ prefixes, p < M) (hs : ∀ z ∈ suffixes, z < B)
    (haccept : ∀ p ∈ prefixes, ∀ z ∈ suffixes, A (p * B + z)) :
    (rectangleValues B prefixes suffixes).length ≤ rM * rB := by
  rw [rectangleValues_length]
  cases prefixes with
  | nil => simp
  | cons p ps =>
    cases suffixes with
    | nil => simp
    | cons z zs =>
      apply Nat.mul_le_mul
      · apply hMbound _ hdp hp
        apply affine_preimage_free (offset := z) (scale := B) hA hB
        intro x hx
        simpa only [Nat.add_comm] using haccept x hx z (List.mem_cons_self ..)
      · apply hBbound _ hds hs
        apply affine_preimage_free (offset := p * B) (scale := 1) hA (by decide)
        intro x hx
        simpa only [Nat.mul_one] using haccept p (List.mem_cons_self ..) x hx

/-- A cover of an AP-free accepted set by s cut-state rectangles gives the
bound s times the two extremal sizes. Rectangles need not be disjoint. -/
theorem rectangle_cover_card_le {k M B rM rB s : Nat}
    (accepted : List Nat) (hd : accepted.Nodup) (hB : 0 < B)
    (hA : APFree k (fun x => x ∈ accepted))
    (hMbound : ExtremalBound k M rM) (hBbound : ExtremalBound k B rB)
    (prefixes suffixes : Fin s → List Nat)
    (hdp : ∀ j, (prefixes j).Nodup) (hds : ∀ j, (suffixes j).Nodup)
    (hp : ∀ j, ∀ p ∈ prefixes j, p < M) (hs : ∀ j, ∀ z ∈ suffixes j, z < B)
    (hsound : ∀ j, ∀ p ∈ prefixes j, ∀ z ∈ suffixes j, p * B + z ∈ accepted)
    (hcover : ∀ x ∈ accepted, ∃ j, ∃ p ∈ prefixes j, ∃ z ∈ suffixes j, p * B + z = x) :
    accepted.length ≤ s * (rM * rB) := by
  apply children_length_le_of_fibre_cover hd
    (fun j => rectangleValues B (prefixes j) (suffixes j))
  · intro x hx
    obtain ⟨j, p, hp', z, hz, heq⟩ := hcover x hx
    exact ⟨j, List.mem_flatMap.mpr ⟨p, hp', List.mem_map.mpr ⟨z, hz, heq⟩⟩⟩
  · intro j
    exact rectangle_card_le hB hA hMbound hBbound _ _ (hdp j) (hds j)
      (hp j) (hs j) (hsound j)

/-- At an actual deterministic cut, the prefix selects one of s states and
each state fixes which suffixes are accepted. This constructs the rectangle
cover from those transition semantics. The two blocks may have unequal size. -/
theorem deterministic_cut_card_le {k M B rM rB s : Nat}
    (accepted : List Nat) (hd : accepted.Nodup) (hB : 0 < B)
    (hA : APFree k (fun x => x ∈ accepted))
    (hMbound : ExtremalBound k M rM) (hBbound : ExtremalBound k B rB)
    (hfull : ∀ x ∈ accepted, x < M * B)
    (state : Nat → Fin s) (future : Fin s → Nat → Prop)
    (hcut : ∀ p, p < M → ∀ z, z < B →
      (p * B + z ∈ accepted ↔ future (state p) z)) :
    accepted.length ≤ s * (rM * rB) := by
  classical
  let prefixes (j : Fin s) := (List.range M).filter (fun p => decide (state p = j))
  let suffixes (j : Fin s) := (List.range B).filter (fun z => decide (future j z))
  have hpre (j : Fin s) (p : Nat) : p ∈ prefixes j ↔ p < M ∧ state p = j := by
    simp [prefixes]
  have hsuf (j : Fin s) (z : Nat) : z ∈ suffixes j ↔ z < B ∧ future j z := by
    simp [suffixes]
  apply rectangle_cover_card_le accepted hd hB hA hMbound hBbound prefixes suffixes
  · exact fun _ => List.nodup_range.filter _
  · exact fun _ => List.nodup_range.filter _
  · exact fun j p hp => ((hpre j p).mp hp).1
  · exact fun j z hz => ((hsuf j z).mp hz).1
  · intro j p hp z hz
    obtain ⟨hp', hj⟩ := (hpre j p).mp hp
    obtain ⟨hz', hf⟩ := (hsuf j z).mp hz
    exact (hcut p hp' z hz').mpr (hj ▸ hf)
  · intro x hx
    have hp : x / B < M := (Nat.div_lt_iff_lt_mul hB).mpr (hfull x hx)
    have hz : x % B < B := Nat.mod_lt x hB
    have hsplit : x / B * B + x % B = x := by
      simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div x B
    refine ⟨state (x / B), x / B, (hpre _ _).mpr ⟨hp, rfl⟩,
      x % B, (hsuf _ _).mpr ⟨hz, (hcut _ hp _ hz).mp ?_⟩, hsplit⟩
    rwa [hsplit]

end DigitProof

namespace DigitProof

/-- The transition may depend on the digit position. -/
def run {s : Nat} (step : Nat → Fin s → Nat → Fin s) :
    Nat → Fin s → List Nat → Fin s
  | _, q, [] => q
  | i, q, x :: xs => run step (i+1) (step i q x) xs

theorem run_append {s : Nat} (step : Nat → Fin s → Nat → Fin s)
    (p u : List Nat) (i : Nat) (q : Fin s) :
    run step i q (p ++ u) = run step (i + p.length) (run step i q p) u := by
  induction p generalizing i q with
  | nil => simp [run]
  | cons x xs ih =>
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (i+1) (step i q x)

def valueFrom (B : Nat) : Nat → List Nat → Nat
  | v, [] => v
  | v, x :: xs => valueFrom B (v * B + x) xs

theorem valueFrom_append (B v : Nat) (p u : List Nat) :
    valueFrom B v (p ++ u) = valueFrom B (valueFrom B v p) u := by
  induction p generalizing v with
  | nil => rfl
  | cons _ _ ih => exact ih _

theorem valueFrom_offset (B a h : Nat) (u : List Nat) :
    valueFrom B (a+h) u = a * B ^ u.length + valueFrom B h u := by
  induction u generalizing a h with
  | nil => simp [valueFrom]
  | cons x xs ih =>
    simp only [valueFrom, Nat.add_mul, Nat.add_assoc, List.length_cons]
    rw [ih, Nat.pow_succ, Nat.mul_comm (B^xs.length) B, Nat.mul_assoc]

private noncomputable def liveAfter (B t : Nat) (accepts : List Nat → Prop)
    (p : List Nat) : List Nat := by
  classical
  exact (List.range B).filter fun x => decide (∃ u : List Nat,
    (p ++ [x] ++ u).length = t ∧ (∀ y ∈ u, y < B) ∧ accepts (p ++ [x] ++ u))

private theorem mem_liveAfter {B t x : Nat} {accepts : List Nat → Prop} {p : List Nat} :
    x ∈ liveAfter B t accepts p ↔ x < B ∧ ∃ u : List Nat,
    (p ++ [x] ++ u).length = t ∧ (∀ y ∈ u, y < B) ∧ accepts (p ++ [x] ++ u) := by
  classical
  simp [liveAfter]

private theorem accepted_follows {B t : Nat} {accepts : List Nat → Prop} (p v : List Nat)
    (ht : (p ++ v).length = t) (hb : ∀ x ∈ v, x < B) (ha : accepts (p ++ v)) :
    Follows (liveAfter B t accepts) p v := by
  induction v generalizing p with
  | nil => trivial
  | cons x xs ih =>
    have ht' : (p ++ [x] ++ xs).length = t := by simpa using ht
    have ha' : accepts (p ++ [x] ++ xs) := by simpa using ha
    have hb' : ∀ y ∈ xs, y < B := fun y hy => hb y (List.mem_cons_of_mem _ hy)
    exact ⟨mem_liveAfter.mpr ⟨hb x (by simp), xs, ht', hb', ha'⟩,
      ih _ ht' hb' ha'⟩

/-- A width-s digit recogniser accepts at most (s*r)^t words when its
accepted integer values are k-AP-free and r bounds k-AP-free sets in [0,B).
Transitions may change after every digit. -/
theorem machine_word_bound {s B t k r : Nat} (hB : 0 < B)
    (step : Nat → Fin s → Nat → Fin s) (start : Fin s) (good : Fin s → Prop)
    (A : Nat → Prop) (hA : APFree k A) (hr : ExtremalBound k B r)
    (hsound : ∀ w : List Nat, w.length = t → (∀ x ∈ w, x < B) →
      good (run step 0 start w) → A (valueFrom B 0 w))
    (words : List (List Nat)) (hd : words.Nodup)
    (hw : ∀ w ∈ words, w.length = t ∧ (∀ x ∈ w, x < B) ∧ good (run step 0 start w)) :
    words.length ≤ (s * r) ^ t := by
  classical
  let accepts := fun w => good (run step 0 start w)
  let valid := fun p : List Nat => ∀ x ∈ p, x < B
  let children := fun p => if valid p then liveAfter B t accepts p else []
  let state := fun (p : List Nat) (x : Nat) => run step 0 start (p ++ [x])
  apply accepted_words_length_le_of_state_fibres children state [] words hd
  · intro p
    dsimp only [children]
    split
    · exact (List.nodup_range).filter _
    · simp
  · intro p j
    by_cases hp : valid p
    · let F := (children p).filter fun x => decide (state p x = j)
      change F.length ≤ r
      have live {x} (hx : x ∈ F) : x ∈ liveAfter B t accepts p := by
        simpa [children,hp] using (List.mem_filter.mp hx).1
      cases heq : F with
      | nil => simp
      | cons z zs =>
        rw [← heq]
        have hz : z ∈ F := by simp [heq]
        obtain ⟨_, u, hu, hub, hau⟩ := mem_liveAfter.mp (live hz)
        have hzs : state p z = j := of_decide_eq_true (List.mem_filter.mp hz).2
        apply liveFibre_length_le (pre := valueFrom B 0 p) (place := B ^ u.length)
          (suffix := valueFrom B 0 u) (A := A) (state p) j F
        · dsimp only [F,children]; rw [if_pos hp]
          exact (List.nodup_range.filter _).filter _
        · exact fun x hx => (mem_liveAfter.mp (live hx)).1
        · exact fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2
        · intro x hx hxj
          have same : run step 0 start ((p ++ [x]) ++ u) =
              run step 0 start ((p ++ [z]) ++ u) := by
            rw [run_append step (p ++ [x]) u, run_append step (p ++ [z]) u]
            simp only [List.length_append, List.length_cons, List.length_nil]
            simpa [state] using congrArg (fun q => run step (0+(p.length+1)) q u)
              (hxj.trans hzs.symm)
          have hacc : good (run step 0 start ((p ++ [x]) ++ u)) := same ▸ hau
          have hlen : (p ++ [x] ++ u).length = t := by simpa using hu
          have hdigits : ∀ y ∈ p ++ [x] ++ u, y < B := by
            intro y hy
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with (h | h) | h
            · exact hp y h
            · simpa [h] using hx
            · exact hub y h
          have hnum := hsound _ hlen hdigits hacc
          rw [valueFrom_append, valueFrom_append] at hnum
          change A (valueFrom B (valueFrom B 0 p * B + x) u) at hnum
          rw [← Nat.add_zero (valueFrom B 0 p * B + x), valueFrom_offset] at hnum
          exact hnum
        · exact Nat.pow_pos hB
        · exact hA
        · exact hr
    · simp [children,hp]
  · intro w hmem
    obtain ⟨hlen, hdigits, hacc⟩ := hw w hmem
    refine ⟨hlen, ?_⟩
    have transfer (p v : List Nat) (hp : valid p) (hv : ∀ y ∈ v, y < B)
        (h : Follows (liveAfter B t accepts) p v) : Follows children p v := by
      induction v generalizing p with
      | nil => trivial
      | cons x xs ih =>
        refine ⟨by simpa [children,hp] using h.1, ih _ ?_ ?_ h.2⟩
        · intro y hy
          simp only [List.mem_append,List.mem_singleton] at hy
          exact hy.elim (hp y) (fun e => e ▸ hv x (by simp))
        · exact fun y hy => hv y (List.mem_cons_of_mem x hy)
    exact transfer [] w (by simp [valid]) hdigits
      (accepted_follows [] w (by simpa using hlen) hdigits (by simpa [accepts] using hacc))

end DigitProof

namespace DigitProof

/-- State after reading the padded length-m ternary expansion of x, most
significant digit first. The transition may change with position. -/
def ternaryState (step : Nat → Bool → Nat → Bool) (start : Bool) : Nat → Nat → Bool
  | 0, _ => start
  | m+1, x => step m (ternaryState step start m (x/3)) (x%3)

def ternaryAccepted (step : Nat → Bool → Nat → Bool) (start : Bool)
    (good : Bool → Bool) (m : Nat) : List Nat :=
  (List.range (3^m)).filter fun x => good (ternaryState step start m x)

theorem mem_ternaryAccepted {step start good m x} :
    x ∈ ternaryAccepted step start good m ↔ x < 3^m ∧ good (ternaryState step start m x) = true := by
  simp [ternaryAccepted]

theorem append_ternaryDigit (step : Nat → Bool → Nat → Bool) (start : Bool)
    (m p z : Nat) (hz : z < 3) :
    ternaryState step start (m+1) (p*3+z) = step m (ternaryState step start m p) z := by
  have hq : (p*3+z)/3=p := by omega
  have hr : (p*3+z)%3=z := by omega
  simp only [ternaryState, hq, hr]

end DigitProof

namespace DigitProof

private def HasOneTriple (v : List Bool) : Prop :=
  ∃ a : Fin 9, ∃ j : Fin 4,
    a.val + 2 * (j.val+1) < 9 ∧
    v[a.val]? = some true ∧ v[a.val+(j.val+1)]? = some true ∧
    v[a.val+2*(j.val+1)]? = some true

private instance (v : List Bool) : Decidable (HasOneTriple v) :=
  inferInstanceAs (Decidable (∃ _a : Fin 9, ∃ _j : Fin 4, _))

private def flags (a b c p q r x y z : Bool) : List Bool :=
  [if a then x else p, if a then y else q, if a then z else r,
   if b then x else p, if b then y else q, if b then z else r,
   if c then x else p, if c then y else q, if c then z else r]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem twoRow_check (a b c p q r x y z : Bool) :
    ((flags a b c p q r x y z).filter id).length ≤ 4 ∨
    HasOneTriple (flags a b c p q r x y z) := by decide +revert

/-- A two-state deterministic machine on two ternary digits cannot recognise
    five or more values unless three of them form a positive-step progression. -/
theorem twoRow_seed (first : Nat → Bool) (last : Bool → Nat → Bool)
    (hf : APFree 3 (fun x => x < 9 ∧ last (first (x/3)) (x%3) = true)) :
    ((List.range 9).filter (fun x => last (first (x/3)) (x%3))).length ≤ 4 := by
  let digit := fun x : Nat => last (first (x/3)) (x%3)
  let v := (List.range 9).map digit
  have hl (b : Bool) (i : Nat) : (if b then last true i else last false i) = last b i := by
    cases b <;> rfl
  have heq : flags (first 0) (first 1) (first 2)
      (last false 0) (last false 1) (last false 2)
      (last true 0) (last true 1) (last true 2) = v := by
    unfold flags
    simp only [hl]
    rfl
  have hc := twoRow_check (first 0) (first 1) (first 2)
      (last false 0) (last false 1) (last false 2)
      (last true 0) (last true 1) (last true 2)
  rw [heq] at hc
  rcases hc with hcard | ⟨a,j,he,h₀,h₁,h₂⟩
  · simpa [v,digit,List.filter_map, Function.comp_def] using hcard
  · have ha : a.val < 9 := a.isLt
    have hm : a.val+(j.val+1) < 9 := by omega
    have at₀ : digit a.val = true := by
      simpa [v,List.getElem?_eq_getElem,ha] using h₀
    have at₁ : digit (a.val+(j.val+1)) = true := by
      simpa [v,List.getElem?_eq_getElem,hm] using h₁
    have at₂ : digit (a.val+2*(j.val+1)) = true := by
      simpa [v,List.getElem?_eq_getElem,he] using h₂
    exfalso
    apply hf a.val (j.val+1) (by omega)
    intro i hi
    have hi' : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi' with rfl | rfl | rfl
    · simpa using And.intro ha at₀
    · simpa using And.intro hm at₁
    · exact ⟨he,at₂⟩
private def HasMonoTriple (colors : List Bool) : Prop :=
  ∃ a : Fin 9, ∃ d : Fin 4,
    a.val + 2 * (d.val + 1) < 9 ∧
    colors[a.val]? = colors[a.val + (d.val + 1)]? ∧
    colors[a.val + (d.val + 1)]? = colors[a.val + 2 * (d.val + 1)]?

private instance (c : List Bool) : Decidable (HasMonoTriple c) :=
  inferInstanceAs (Decidable (∃ _a : Fin 9, ∃ _d : Fin 4, _))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem allNine (a b c d e f g h i : Bool) :
    HasMonoTriple [a,b,c,d,e,f,g,h,i] := by decide +revert

theorem everyTwoColouring_has_three (c : Nat → Bool) :
    ∃ a d : Nat, 0 < d ∧ a+2*d < 9 ∧ c a = c (a+d) ∧ c (a+d) = c (a+2*d) := by
  have h : HasMonoTriple ((List.range 9).map c) := allNine _ _ _ _ _ _ _ _ _
  obtain ⟨a,d,hfit,h1,h2⟩ := h
  have ha : a.val < 9 := a.isLt
  have ha' : a.val + (d.val+1) < 9 := by omega
  refine ⟨a.val,d.val+1,by omega,hfit,?_,?_⟩
  · simpa [List.getElem?_eq_getElem, ha, ha'] using h1
  · simpa [List.getElem?_eq_getElem, ha', hfit] using h2

/-- A two-colouring of the first eight integers having no monochromatic
    three-term progression. Together with the previous theorem this gives W(2,3)=9. -/
theorem eightTwoColouring_without_three :
    ∃ c : Nat → Bool, ∀ a d : Nat, 0 < d → a+2*d < 8 →
      ¬ (c a = c (a+d) ∧ c (a+d) = c (a+2*d)) := by
  refine ⟨fun x => decide (x/2%2=1), ?_⟩
  intro a d hd he
  simp only [decide_eq_decide]
  omega

theorem ternary_mono9 (f : Nat → Bool) :
    ∃ a d : Nat, 0 < d ∧ a + 2*d < 9 ∧
      f a = f (a+d) ∧ f a = f (a+2*d) := by
  obtain ⟨a,d,hd,he,h₁,h₂⟩ := everyTwoColouring_has_three f
  exact ⟨a,d,hd,he,h₁,h₁.trans h₂⟩

end DigitProof

namespace DigitProof

/-- Length-m ternary strings with digits 0 and 1, interpreted as integers. -/
def CantorLayer : Nat → Nat → Prop
  | 0, v => v = 0
  | m+1, v => ∃ u, CantorLayer m u ∧ ∃ e < 2, v = u * 3 + e

private theorem cantor_midpoint {m x y z : Nat} (hx : CantorLayer m x)
    (hy : CantorLayer m y) (hz : CantorLayer m z) (he : x + z = y + y) : x = y := by
  induction m generalizing x y z with
  | zero => simp_all [CantorLayer]
  | succ m ih =>
    obtain ⟨a, ha, i, hi, rfl⟩ := hx
    obtain ⟨b, hb, j, hj, rfl⟩ := hy
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    have digits : i = j ∧ l = j := by
      have h (d : Nat) (hd : d < 2) : d = 0 ∨ d = 1 := by omega
      rcases h i hi with rfl | rfl <;> rcases h j hj with rfl | rfl <;>
        rcases h l hl with rfl | rfl <;> omega
    have hmid : a + c = b + b := by omega
    have hab := ih ha hb hc hmid
    omega

theorem cantor_layer_apFree (m : Nat) : APFree 3 (CantorLayer m) := by
  intro a d hd hall
  have hx := hall 0 (by decide)
  have hy := hall 1 (by decide)
  have hz := hall 2 (by decide)
  have he := cantor_midpoint hx hy hz (by omega)
  omega

/-- The live state survives exactly while each digit is 0 or 1. -/
def cantorStep (_ : Nat) (q : Bool) (d : Nat) : Bool := q && decide (d < 2)

theorem mem_cantorAccepted (m x : Nat) :
    x ∈ ternaryAccepted cantorStep true id m ↔ CantorLayer m x := by
  induction m generalizing x with
  | zero =>
    simp [mem_ternaryAccepted, ternaryState, CantorLayer]
  | succ m ih =>
    constructor
    · intro hx
      obtain ⟨hB, hx⟩ := mem_ternaryAccepted.mp hx
      simp only [id_eq, ternaryState, cantorStep, Bool.and_eq_true, decide_eq_true_eq] at hx
      have hprev : x/3 ∈ ternaryAccepted cantorStep true id m := by
        apply mem_ternaryAccepted.mpr
        rw [Nat.pow_succ] at hB
        exact ⟨by omega, hx.1⟩
      exact ⟨x/3, (ih _).mp hprev, x%3, hx.2, by omega⟩
    · rintro ⟨v, hv, e, he, rfl⟩
      obtain ⟨hB, hs⟩ := mem_ternaryAccepted.mp ((ih _).mpr hv)
      apply mem_ternaryAccepted.mpr
      constructor
      · rw [Nat.pow_succ]
        omega
      · rw [append_ternaryDigit _ _ _ _ _ (by omega)]
        simpa [cantorStep, he] using hs

private def cantorValues : Nat → List Nat
  | 0 => [0]
  | m+1 => (cantorValues m).map (fun v => v*3) ++
      (cantorValues m).map (fun v => v*3+1)

private theorem cantorValues_length (m : Nat) : (cantorValues m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [cantorValues, ih, Nat.pow_succ, Nat.mul_two]

private theorem cantorValues_nodup (m : Nat) : (cantorValues m).Nodup := by
  induction m with
  | zero => simp [cantorValues]
  | succ m ih =>
    apply List.nodup_append.mpr
    refine ⟨List.Pairwise.map _ (fun a b h eq => h (by omega)) ih,
      List.Pairwise.map _ (fun a b h eq => h (by omega)) ih, ?_⟩
    intro x hx y hy e
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    omega

private theorem mem_cantorValues (m x : Nat) : x ∈ cantorValues m ↔ CantorLayer m x := by
  induction m generalizing x with
  | zero => simp [cantorValues, CantorLayer]
  | succ m ih =>
    simp only [cantorValues, List.mem_append, List.mem_map, CantorLayer]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact ⟨v, (ih _).mp hv, 0, by decide, rfl⟩
      · exact ⟨v, (ih _).mp hv, 1, by decide, rfl⟩
    · rintro ⟨v, hv, e, he, rfl⟩
      have hcases : e = 0 ∨ e = 1 := by omega
      rcases hcases with rfl | rfl
      · exact Or.inl ⟨v, (ih _).mpr hv, rfl⟩
      · exact Or.inr ⟨v, (ih _).mpr hv, rfl⟩

/-- A fixed two-state recogniser attains exactly 2^m values at every length;
all accepted sets avoid three-term arithmetic progressions. -/
theorem cantor_two_state_attains (m : Nat) :
    APFree 3 (fun x => x ∈ ternaryAccepted cantorStep true id m) ∧
    (ternaryAccepted cantorStep true id m).length = 2 ^ m := by
  constructor
  · intro a d hd terms
    exact cantor_layer_apFree m a d hd (fun i hi => (mem_cantorAccepted m _).mp (terms i hi))
  · rw [← cantorValues_length m]
    apply Nat.le_antisymm
    · have hn : (ternaryAccepted cantorStep true id m).Nodup := List.nodup_range.filter _
      apply hn.length_le_of_subset
      intro x hx
      exact (mem_cantorValues _ _).mpr ((mem_cantorAccepted _ _).mp hx)
    · apply (cantorValues_nodup m).length_le_of_subset
      intro x hx
      exact (mem_cantorAccepted _ _).mpr ((mem_cantorValues _ _).mp hx)

end DigitProof

namespace DigitProof

private theorem three_steps {a d : Nat} {P : Nat → Prop}
    (h₀ : P a) (h₁ : P (a+d)) (h₂ : P (a+2*d)) : ∀ i, i<3 → P (a+i*d) := by
  intro i hi
  have : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases this with rfl | rfl | rfl <;> simpa using ‹_›

private theorem small_prefix {m : Nat} (hm : 2 ≤ m) : 9 ≤ 3^m := by
  exact Nat.pow_le_pow_right (by decide : 0 < 3) hm

/-- After at least two input digits there is a state with no accepting
last digit. Colour the first nine prefixes by their state. -/
private theorem dead_before_last (step : Nat → Bool → Nat → Bool) (start : Bool)
    (good : Bool → Bool) (m : Nat) (hm : 2 ≤ m)
    (hf : APFree 3 (fun x => x ∈ ternaryAccepted step start good (m+1))) :
    ∃ dead : Bool, ∀ z, z < 3 → good (step m dead z) = false := by
  obtain ⟨a,d,hd,ha,h₁,h₂⟩ := ternary_mono9 (ternaryState step start m)
  refine ⟨ternaryState step start m a, ?_⟩
  intro z hz
  cases he : good (step m (ternaryState step start m a) z) with
  | false => rfl
  | true =>
    exfalso
    apply hf (a*3+z) (d*3) (by omega)
    have extend (p : Nat) (hp : p < 9)
        (hs : ternaryState step start m a = ternaryState step start m p) :
        p*3+z ∈ ternaryAccepted step start good (m+1) := by
      apply mem_ternaryAccepted.mpr
      rw [Nat.pow_succ,append_ternaryDigit _ _ _ _ _ hz,← hs]
      have := small_prefix hm
      exact ⟨by omega,he⟩
    apply three_steps
    · exact extend a (by omega) rfl
    · simpa only [Nat.add_mul, Nat.add_right_comm] using extend (a+d) (by omega) h₁
    · have HH := extend (a+2*d) ha h₂
      rw [Nat.add_mul, Nat.mul_assoc 2, Nat.add_right_comm] at HH
      exact HH

/-- In a two-state ternary recogniser, any accepted 3-AP-free language
on m digits has at most 2^m elements. -/
theorem ternary_two_state_upper (step : Nat → Bool → Nat → Bool) (start : Bool)
    (m : Nat) (good : Bool → Bool)
    (hf : APFree 3 (fun x => x ∈ ternaryAccepted step start good m)) :
    (ternaryAccepted step start good m).length ≤ 2^m := by
  induction m generalizing good with
  | zero =>
    exact Nat.le_trans (List.length_filter_le ..) (by simp)
  | succ m ih =>
    by_cases hzero : m = 0
    · subst m
      have H := List.length_filter_le (fun x => good (ternaryState step start 1 x)) (List.range 3)
      apply Nat.le_of_not_lt
      intro big
      have he : (ternaryAccepted step start good 1).length = (List.range 3).length := by
        change ((List.range 3).filter _).length ≤ _ at H
        change 2^1 < ((List.range 3).filter _).length at big
        change ((List.range 3).filter _).length = _
        simp at H big ⊢; omega
      have heq : ternaryAccepted step start good 1 = List.range 3 := by
        apply List.Sublist.eq_of_length (List.filter_sublist ..) he
      apply hf 0 1 (by decide)
      intro i hi
      simp [heq,hi]
    by_cases hone : m = 1
    · subst m
      let first := ternaryState step start 1
      let last := fun q x => good (step 1 q x)
      exact twoRow_seed first last (by
        intro a d hd hall
        apply hf a d hd
        intro i hi
        exact mem_ternaryAccepted.mpr (hall i hi))
    obtain ⟨dead,hdead⟩ := dead_before_last step start good m (by omega) hf
    let live := !dead
    let pref := ternaryAccepted step start (fun q => decide (q=live)) m
    let digs := (List.range 3).filter fun z => good (step m live z)
    let full := ternaryAccepted step start good (m+1)
    change full.length ≤ _
    by_cases hne : full = []
    · simp [hne]
    obtain ⟨v,hv⟩ := List.exists_mem_of_ne_nil _ hne
    have split (x : Nat) (hx : x ∈ full) :
        x / 3 ∈ pref ∧ x % 3 ∈ digs := by
      obtain ⟨hx',ha⟩ := mem_ternaryAccepted.mp hx
      rw [Nat.pow_succ] at hx'
      have he : ternaryState step start m (x/3) = live := by
        apply Classical.byContradiction
        intro hn
        have eq : ternaryState step start m (x/3) = dead := by
          cases dead <;> cases H : ternaryState step start m (x/3) <;> simp_all [live]
        rw [ternaryState,eq,hdead _ (by omega)] at ha
        contradiction
      refine ⟨mem_ternaryAccepted.mpr ⟨by omega, by simp [he]⟩,
        List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩⟩
      simpa [ternaryState, he] using ha
    have join {p z : Nat} (hp : p ∈ pref) (hz : z ∈ digs) : p*3+z ∈ full := by
      obtain ⟨hp',he⟩ := mem_ternaryAccepted.mp hp
      have hj : ternaryState step start m p = live := of_decide_eq_true he
      obtain ⟨hz',hdig⟩ := List.mem_filter.mp hz
      have hlt := List.mem_range.mp hz'
      apply mem_ternaryAccepted.mpr
      rw [Nat.pow_succ,append_ternaryDigit _ _ _ _ _ hlt,hj]
      exact ⟨by omega,hdig⟩
    obtain ⟨hvp,hvd⟩ := split v hv
    have ph : APFree 3 (fun x => x ∈ pref) := by
      apply affine_preimage_free (offset := v%3) (scale := 3) hf (by decide)
      intro x hx
      simpa [Nat.add_comm] using join hx hvd
    have dh : digs.length ≤ 2 := by
      apply Nat.le_of_not_lt
      intro big
      have hlen : digs.length = (List.range 3).length := by
        have hlim : digs.length ≤ (List.range 3).length := List.length_filter_le ..
        simp at hlim ⊢; omega
      have eq : digs = List.range 3 := List.Sublist.eq_of_length (List.filter_sublist ..) hlen
      apply hf (v/3*3) 1 (by decide)
      intro i hi
      simpa using join hvp (show i ∈ digs by simp [eq,hi])
    have hh : full ⊆ rectangleValues 3 pref digs := by
      intro x hx
      obtain ⟨hp,hz⟩ := split x hx
      refine List.mem_flatMap.mpr ⟨x/3,hp,List.mem_map.mpr ⟨x%3,hz,?_⟩⟩
      omega
    have nodup : full.Nodup := List.nodup_range.filter _
    calc
      _ ≤ (rectangleValues 3 pref digs).length := nodup.length_le_of_subset hh
      _ = pref.length * digs.length := rectangleValues_length ..
      _ ≤ (2^m)*2 := Nat.mul_le_mul (ih _ ph) dh
      _ = 2^(m+1) := (Nat.pow_succ ..).symm

end DigitProof

namespace DigitProof

/-- Progression-freeness in the pinned library excludes all positive-step
integer progressions of the given length when at least two terms are required. -/
theorem apFree_of_pinned {k : Nat} {A : Set Nat} (hk : 2 ≤ k)
    (hA : A.IsAPOfLengthFree k) : APFree k A := by
  intro a d hd terms
  let T := (Finset.range k).image (fun i => a + i * d)
  have mem_T (v : Nat) : v ∈ T ↔ ∃ i < k, a + i * d = v := by
    simp [T]
  have sub : (T : Set Nat) ⊆ A := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := (mem_T v).mp hv
    exact terms i hi
  have hap : (T : Set Nat).IsAPOfLength k := by
    refine ⟨a, d, ?_, ?_⟩
    · have inj : Function.Injective (fun i : Nat => a + i * d) :=
        fun _ _ h => Nat.mul_right_cancel hd (Nat.add_left_cancel h)
      change ENat.card T = k
      rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe,
        Finset.card_image_of_injective _ inj, Finset.card_range]
    · ext v
      change v ∈ T ↔ _
      simpa only [Set.mem_ofPred_eq, ENat.natCast_lt_natCast, nsmul_eq_mul,
        Nat.cast_id, exists_prop] using mem_T v
  have hk' : k ≤ 1 := by exact_mod_cast hA _ sub hap
  omega

/-- The extremal function from Erdős #142 bounds the AP-free block fibres.
The pinned definition takes subsets of [1,B], so translate each block by one. -/
theorem pinned_extremalBound {k B : Nat} (hk : 2 ≤ k) :
    ExtremalBound k B (Set.IsAPOfLengthFree.maxCard k B) := by
  classical
  intro xs hxs hB hfree
  let S := (xs.map Nat.succ).toFinset
  have mem_S (v : Nat) : v ∈ S ↔ ∃ x ∈ xs, Nat.succ x = v := by
    simp [S]
  have sub : S ⊆ Finset.Icc 1 B := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (mem_S v).mp hv
    exact Finset.mem_Icc.mpr ⟨by omega, hB x hx⟩
  have free_S : (S : Set Nat).IsAPOfLengthFree k := by
    rintro T hTS ⟨a, d, hcard, hT⟩
    have in_S (i : Nat) (hi : i < k) : a + i * d ∈ S := by
      apply hTS
      rw [hT]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hk' : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    have hd : 0 < d := by
      by_contra hd
      have hzero : d = 0 := by omega
      have eq_singleton : T = {a} := by
        rw [hT, hzero]
        ext u
        simp only [nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, hi, rfl⟩
          rfl
        · rintro rfl
          exact ⟨0, hk', rfl⟩
      rw [eq_singleton] at hcard
      have hk_one : k = 1 := by simpa using hcard.symm
      omega
    have ha : 1 ≤ a := by
      have haS : a ∈ S := by simpa using in_S 0 (by omega)
      exact (Finset.mem_Icc.mp (sub haS)).1
    exfalso
    apply hfree (a - 1) d hd
    intro i hi
    obtain ⟨x, hx, hxv⟩ := (mem_S _).mp (in_S i hi)
    have eq_x : a - 1 + i * d = x := by omega
    exact eq_x ▸ hx
  have hcard_S : S.card = xs.length := by
    simpa [S] using List.toFinset_card_of_nodup
      (hxs.map (show Function.Injective Nat.succ from Nat.succ_injective))
  unfold Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨(Finset.Icc 1 B).card, ?_⟩
    rintro _ ⟨S', hS', _, rfl⟩
    exact Finset.card_le_card hS'
  · exact ⟨S, sub, free_S, hcard_S⟩

end DigitProof

namespace DigitProof

/-- The coordinates at which a finite vector is nonzero. -/
noncomputable def nonzeroIndices {ι K : Type*} [Fintype ι] [Zero K]
    (v : ι → K) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => v i ≠ 0)

@[simp]
theorem mem_nonzeroIndices {ι K : Type*} [Fintype ι] [Zero K]
    {v : ι → K} {i : ι} : i ∈ nonzeroIndices v ↔ v i ≠ 0 := by
  classical
  simp [nonzeroIndices]

/-- The supports of a basis chosen from the matrix columns cover every
nonzero row. This bounds how many different block values can be completed
when columns index possible suffixes. -/
theorem nonzero_rows_le_rank_mul {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    (A : Matrix I J K) {colBound : Nat}
    (hcol : ∀ j, (nonzeroIndices (A.col j)).card ≤ colBound) :
    (nonzeroIndices (fun i => A i)).card ≤ A.rank * colBound := by
  classical
  obtain ⟨κ, a, hinj, hspan, hli⟩ := exists_linearIndependent' K A.col
  let : Finite κ := Finite.of_injective a hinj
  let := Fintype.ofFinite κ
  have hdim : Fintype.card κ = A.rank := by
    rw [A.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  let rows := Finset.univ.biUnion (fun t : κ => nonzeroIndices (A.col (a t)))
  have hrows : rows.card ≤ A.rank * colBound := by
    calc
      rows.card ≤ ∑ t : κ, (nonzeroIndices (A.col (a t))).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : κ, colBound := Finset.sum_le_sum (fun t _ => hcol (a t))
      _ = A.rank * colBound := by simp [hdim]
  have live {i j} (h : A i j ≠ 0) : i ∈ rows := by
    by_contra hnone
    have hzero (t : κ) : A i (a t) = 0 := by
      by_contra hn
      exact hnone (Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_univ _, mem_nonzeroIndices.mpr hn⟩)
    have hker : Submodule.span K (Set.range (A.col ∘ a)) ≤
        LinearMap.ker (LinearMap.proj i : (I → K) →ₗ[K] K) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, rfl⟩
      exact hzero t
    have hmem : A.col j ∈ Submodule.span K (Set.range (A.col ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact h (hker hmem)
  apply (Finset.card_le_card (t := rows) ?_).trans hrows
  intro i hi
  by_contra h
  apply mem_nonzeroIndices.mp hi
  funext j
  by_contra hn
  exact h (live hn)

/-- The nonzero entries of a matrix are counted by its field rank times an
upper bound on the number of nonzero entries in a row and in a column. -/
theorem nonzero_entries_le_rank_mul {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    (A : Matrix I J K) {rowBound colBound : Nat}
    (hrow : ∀ i, (nonzeroIndices (A i)).card ≤ rowBound)
    (hcol : ∀ j, (nonzeroIndices (A.col j)).card ≤ colBound) :
    (nonzeroIndices (fun ij : I × J => A ij.1 ij.2)).card ≤
      A.rank * (colBound * rowBound) := by
  classical
  let rows := nonzeroIndices (fun i => A i)
  have hrows : rows.card ≤ A.rank * colBound := nonzero_rows_le_rank_mul A hcol
  have live {i j} (h : A i j ≠ 0) : i ∈ rows :=
    mem_nonzeroIndices.mpr (fun hz => h (congrFun hz j))
  have hsum : (∑ i ∈ rows, (nonzeroIndices (A i)).card) =
      ∑ i : I, (nonzeroIndices (A i)).card := by
    apply Finset.sum_subset (Finset.subset_univ rows)
    intro i _ hi
    apply Finset.card_eq_zero.mpr
    exact Finset.eq_empty_iff_forall_notMem.mpr
      (fun j hj => hi (live (mem_nonzeroIndices.mp hj)))
  calc
    (nonzeroIndices (fun ij : I × J => A ij.1 ij.2)).card =
        ∑ i : I, (nonzeroIndices (A i)).card := by
      simp only [nonzeroIndices, Finset.card_filter, Fintype.sum_prod_type]
    _ = ∑ i ∈ rows, (nonzeroIndices (A i)).card := hsum.symm
    _ ≤ ∑ _ ∈ rows, rowBound := Finset.sum_le_sum fun i _ => hrow i
    _ = rows.card * rowBound := by simp
    _ ≤ A.rank * (colBound * rowBound) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right rowBound hrows

/-- An affine copy of a vector's support inside an AP-free set bounds the
number of nonzero coordinates of that vector. -/
theorem affine_nonzero_card_le {K : Type*} [Zero K] {k M r offset place : Nat}
    {A : Nat → Prop} (v : Fin M → K) (hA : APFree k A) (hplace : 0 < place)
    (hr : ExtremalBound k M r)
    (hsound : ∀ i : Fin M, v i ≠ 0 → A (offset + i.val * place)) :
    (nonzeroIndices v).card ≤ r := by
  classical
  let xs := (nonzeroIndices v).toList.map Fin.val
  have hmem (x : Nat) : x ∈ xs ↔ ∃ i : Fin M, v i ≠ 0 ∧ i.val = x := by
    simp [xs]
  have hd : xs.Nodup := (nonzeroIndices v).nodup_toList.map Fin.val_injective
  have hb (x : Nat) (hx : x ∈ xs) : x < M := by
    obtain ⟨i, _, rfl⟩ := (hmem x).mp hx
    exact i.isLt
  have hf : APFree k (fun x => x ∈ xs) := by
    apply affine_preimage_free (offset := offset) (scale := place) hA hplace
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmem x).mp hx
    exact hsound i hi
  simpa [xs] using hr xs hd hb hf

/-- A cut matrix may have arbitrary field-valued entries. If the integers
represented by its nonzero entries form an AP-free set, its support obeys
the rank bound, with the two interval extremal sizes as factors. -/
theorem apfree_entries_le_rank_mul {K : Type*} [Field K] {k M B rM rB : Nat}
    {A : Nat → Prop} (H : Matrix (Fin M) (Fin B) K) (hA : APFree k A) (hB : 0 < B)
    (hMbound : ExtremalBound k M rM) (hBbound : ExtremalBound k B rB)
    (hsound : ∀ i j, H i j ≠ 0 → A (i.val * B + j.val)) :
    (nonzeroIndices (fun ij : Fin M × Fin B => H ij.1 ij.2)).card ≤
      H.rank * (rM * rB) := by
  apply nonzero_entries_le_rank_mul
  · intro i
    apply affine_nonzero_card_le _ hA (show 0 < 1 by decide) hBbound
      (offset := i.val * B)
    intro j hj
    simpa using hsound i j hj
  · intro j
    apply affine_nonzero_card_le _ hA hB hMbound (offset := j.val)
    intro i hi
    simpa only [Nat.add_comm] using hsound i j hi

end DigitProof

namespace DigitProof

/-- Exact maximum among all two-state, most-significant-first ternary
recognisers; start state, transitions and acceptance are arbitrary. -/
theorem ternary_two_state_exact (m : Nat) :
    (∀ (step : Nat → Bool → Nat → Bool) (start : Bool) (good : Bool → Bool),
      APFree 3 (fun x => x ∈ ternaryAccepted step start good m) →
      (ternaryAccepted step start good m).length ≤ 2^m) ∧
    (∃ (step : Nat → Bool → Nat → Bool) (start : Bool) (good : Bool → Bool),
      APFree 3 (fun x => x ∈ ternaryAccepted step start good m) ∧
      (ternaryAccepted step start good m).length = 2^m) :=
  ⟨fun step start good => ternary_two_state_upper step start m good,
    cantorStep, true, id, cantor_two_state_attains m⟩

theorem pinned_rank_bound {K : Type*} [Field K] {k M B : Nat} (hk : 2 ≤ k)
    {A : Set Nat} (H : Matrix (Fin M) (Fin B) K)
    (hA : A.IsAPOfLengthFree k) (hB : 0 < B)
    (hsound : ∀ i j, H i j ≠ 0 → i.val * B + j.val ∈ A) :
    (nonzeroIndices (fun ij : Fin M × Fin B => H ij.1 ij.2)).card ≤
      H.rank * (Set.IsAPOfLengthFree.maxCard k M * Set.IsAPOfLengthFree.maxCard k B) :=
  apfree_entries_le_rank_mul H (apFree_of_pinned hk hA) hB
    (pinned_extremalBound hk) (pinned_extremalBound hk) hsound

private def witness27 : List Nat := [0,1,4,6,10,15,17,18,22,23,25]

/-- Already at three ternary digits the unrestricted value exceeds 8. -/
theorem unrestricted_at_27 : 11 ≤ Set.IsAPOfLengthFree.maxCard 3 27 := by
  apply pinned_extremalBound (by decide : 2 ≤ 3) witness27 (by decide)
  · intro x hx
    simp [witness27] at hx
    omega
  · intro a d hd h
    have h₀ := h 0 (by decide)
    have h₁ := h 1 (by decide)
    have h₂ := h 2 (by decide)
    simp [witness27] at h₀ h₁ h₂
    omega

end DigitProof
