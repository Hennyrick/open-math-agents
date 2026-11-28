import Erdos142DigitBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Dyadic density windows for unrestricted progression-free sets

This note continues Erdős 142 (isTheta). The companion import is the
file research/Erdos142DigitBounds.lean on this branch. Compile it first
with Lean 4.33.1 in formal-conjectures 9097e2f90e66, then add its olean
directory to LEAN_PATH. All extremal quantities below are the pinned ones.

## A consequence on paper

Fix k >= 3. Write r(N) for the unrestricted extremum, rho(N)=r(N)/N
and D(j)=-log rho(2^j). For large integers J set h=floor(J^(1/3)).
With O(J^(11/12)) exceptions among the indices J <= j < 2J, the
following holds simultaneously for every 2^j <= N < 2^(j+1) and every
AP P in [1,N] of length m >= N/2^h and positive common difference.
Every k-AP-free A in [1,N] satisfies

    |A intersect P| / m <= (1 + O(J^(-1/12))) rho(N).

In particular, take any extremiser A and distribute uniform probability
on its elements. For all q <= 2^(h-1) simultaneously, the distribution
of x mod q is within O(J^(-1/12)) of uniform in total variation.
The bound also holds, with an extra O(eta), if |A| >= (1-eta)r(N)
and 0 <= eta <= 1/2.

Proof. Packing intervals gives r(N) <= ceil(N/B)r(B); in particular
D is nondecreasing. Behrend's lower construction for k=3 works for
every k>=3, giving D(t)=O(sqrt(t)). By exceptional_windows with
n=2J, w=4h and e=J^(-1/12), at most O(h sqrt(J)/e) = O(J^(11/12))
indices j have D(j+2h)-D(j-2h)>=e (put i=j-2h).
For any remaining j let L=2^(j-2h), U=2^(j+2h). Pulling A intersect P
back to its indices and partitioning into blocks of length L gives
density at most (1+L/m)rho(L). Conversely rho(U) <= (1+N/U)rho(N).
The ratio rho(L)/rho(U) is at most exp(e), and L/m <= 2^(-h),
N/U <= 2^(1-2h). Multiplication proves the first assertion.
Each residue class has size floor(N/q) or ceil(N/q) and hence qualifies.
Its probability under the extremiser is at most
(1+O(e))(1/q+1/N). Summing positive excess over uniform costs O(e+q/N).
Normalising a near-extremiser costs a further factor 1/(1-eta).

The finite AP bounds, dyadic monotonicity, and the exceptional-window
inequality are checked below. The use of Behrend and the asymptotic
corollaries above are written mathematics. They provide no bound on
how much density can be lost on an individual exceptional window.

## Why the exceptional lengths cannot be removed by these estimates alone

The following countermodels are functions on lengths, not AP-free sets.
Let T(t) be the sum over integers j >= 2 of min(1,max(0,t-j^2)), for t>=0.
Take c=15/16 or 31/32 and define f(n)=n c^T(log_2 n), g(n)=ceil(f(n))
for n>=1, with g(0)=0. Then for each choice of c:

* g is nondecreasing, integer-valued, has increments 0 or 1, and is subadditive.
  Indeed the ramps are disjoint and T is nondecreasing and 1-Lipschitz.
  Thus f is increasing and f(n)/n is nonincreasing, which gives subadditivity
  of f by bounding the two parts of f(n+m). Taking ceilings preserves
  subadditivity. Use g(1)=1 for the increment bound.
* g(3n)>=2g(n) and g(2mn)>=g(m)g(n). To see this, f(n)=n for n<=16,
  and thereafter f(n)>=16, so g(n)<=17f(n)/16 everywhere.
  A shift in t by log_2(3) hits at most one ramp, so f(3n)>=3c f(n).
  Also sqrt(t)-2 <= T(t) <= sqrt(t): on a ramp starting at j^2 the
  lower bound uses sqrt(j^2+u)<=j+u for 0<=u<=1; between ramps it
  follows by counting completed ramps. Thus
  T(x+y+1)<=T(x)+T(y)+5, whence f(2mn)>=2c^5 f(m) f(n).
  Both constants dominate the requisite ceiling losses.
* g(n)=n exp(-Theta(sqrt(log n))), but along n=2^(j^2),
  g(2n)/(2g(n)) tends to c<1. The two choices of c give functions
  whose ratio tends to infinity, so they have no common Theta scale.

The two multiplicative inequalities are genuine constraints on unrestricted
r_3: append ternary digit 0 or 1 for the first. For the second, use
2n*a+b with a and b drawn from zero-based 3-AP-free sets of lengths m and n.
A midpoint equation mod 2n for the b digits has absolute defect <2n, hence
is an integer equality, so all low digits, then all high digits, agree.
Thus even adding these product constructions does not distinguish the two
orders. This countermodel argument is on paper.

Related work: J. Pollard and OpenAI Codex, Counting progression-free
subsets at almost every logarithmic scale (27 November 2026), also use
averaged extremal-density changes. No claim of priority for that method.
https://projectdiderot.com/papers/4d2b4f71-0035-4612-a67e-d0ed7ff74d7d
Behrend-type lower bounds: https://arxiv.org/abs/2406.12290
-/

open Finset
namespace ScaleWindows
open DigitProof

/-- Split the indices of any arithmetic progression into Q blocks of length B.
The progression need not be aligned to the ambient interval. Only the selected
indices must map to the AP-free set. -/
theorem ap_block_cover {k Q B a d : ℕ} (hk : 2 ≤ k) (hB : 0 < B) (hd : 0 < d)
    {A : Set ℕ} (hA : A.IsAPOfLengthFree k) (indices : List ℕ) (hn : indices.Nodup)
    (hr : ∀ x ∈ indices, x < Q*B) (hmem : ∀ x ∈ indices, a+x*d ∈ A) :
    indices.length ≤ Q * Set.IsAPOfLengthFree.maxCard k B := by
  classical
  let partials (j : Fin Q) := (List.range B).filter fun u => decide (a+(j.val*B+u)*d ∈ A)
  let chunks (j : Fin Q) := (partials j).map (fun u => j.val*B+u)
  apply children_length_le_of_fibre_cover hn chunks
  · intro x hx
    let j : Fin Q := ⟨x/B, (Nat.div_lt_iff_lt_mul hB).mpr (hr x hx)⟩
    have he : j.val * B + x%B = x := by
      simpa [j,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div x B
    refine ⟨j,List.mem_map.mpr ⟨x%B, List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ hB), ?_⟩,he⟩⟩
    simpa [he] using hmem x hx
  · intro j
    change ((partials j).map _).length ≤ _
    rw [List.length_map]
    apply pinned_extremalBound hk (partials j) (List.nodup_range.filter _)
    · exact fun u hu => List.mem_range.mp (List.mem_filter.mp hu).1
    · apply affine_preimage_free (offset := a+j.val*B*d) (scale := d) (apFree_of_pinned hk hA) hd
      intro u hu
      have hu' : a+(j.val*B+u)*d ∈ A := of_decide_eq_true (List.mem_filter.mp hu).2
      change a+j.val*B*d+u*d ∈ A
      simpa [Nat.add_mul,Nat.add_assoc] using hu'

/-- No regularity assumption beyond monotonicity is needed for this overlap bound. -/
theorem window_sum (D : ℕ → ℝ) (hd : Monotone D) (n w : ℕ) :
    (∑ i ∈ range n, (D (i+w)-D i)) ≤ (w:ℝ)*(D (n+w)-D 0) := by
  induction w with
  | zero => simp
  | succ w ih =>
    have increments : (∑ i ∈ range n, (D (i+w+1)-D (i+w))) = D (n+w)-D w := by
      clear ih
      induction n with
      | zero => simp
      | succ n h =>
        rw [sum_range_succ,h]
        simp only [Nat.succ_add]
        ring
    have spl : (∑ i ∈ range n, (D (i+w.succ)-D i)) =
        (∑ i ∈ range n, (D (i+w)-D i)) + (D (n+w)-D w) := by
      rw [← increments, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      rw [Nat.add_succ]
      ring
    rw [spl,Nat.cast_succ,add_mul,one_mul]
    have h₁ := hd (show n+w ≤ n+w.succ by omega)
    have h₂ := hd (Nat.zero_le w)
    have h₃ := mul_le_mul_of_nonneg_left (sub_le_sub_right h₁ (D 0)) (Nat.cast_nonneg w : (0:ℝ) ≤ w)
    linarith

/-- Every unrestricted extremum obeys the block comparison, including when
the last block is incomplete. -/
theorem block_comparison {k N Q B : ℕ} (hk : 2 ≤ k) (hB : 0 < B) (hN : N ≤ Q*B) :
    Set.IsAPOfLengthFree.maxCard k N ≤ Q * Set.IsAPOfLengthFree.maxCard k B := by
  apply csSup_le'
  rintro _ ⟨S,hS,hf,rfl⟩
  let I := S.toList.map (fun x => x-1)
  have bounds {x} (hx : x ∈ S.toList) : 1 ≤ x ∧ x ≤ N :=
    Finset.mem_Icc.mp (hS (Finset.mem_toList.mp hx))
  have hi : I.Nodup := by
    apply List.Nodup.map_on _ S.nodup_toList
    intro x hx y hy he
    have := bounds hx
    have := bounds hy
    omega
  have hr : ∀ x ∈ I, x < Q*B := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have := bounds hy
    omega
  have hm : ∀ x ∈ I, 1+x*1 ∈ (S : Set ℕ) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have := bounds hy
    have he : 1+(y-1)*1=y := by omega
    rw [he]; exact Finset.mem_toList.mp hy
  simpa [I] using ap_block_cover hk hB (by decide : 0 < 1) hf I hi hr hm

/-- Finite bound on the number of windows with density loss at least e. -/
theorem exceptional_windows (D : ℕ → ℝ) (hd : Monotone D) (n w : ℕ) (e : ℝ) :
    (((range n).filter (fun i => e ≤ D (i+w)-D i)).card : ℝ) * e ≤
      (w:ℝ)*(D (n+w)-D 0) := by
  classical
  let bad := (range n).filter (fun i => e ≤ D (i+w)-D i)
  calc
    _ = ∑ _i ∈ bad, e := by simp [bad]
    _ ≤ ∑ i ∈ bad, (D (i+w)-D i) := sum_le_sum fun i hi => (mem_filter.mp hi).2
    _ ≤ ∑ i ∈ range n, (D (i+w)-D i) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => sub_nonneg.mpr (hd (by omega)))
    _ ≤ _ := window_sum D hd n w

local notation "r" => Set.IsAPOfLengthFree.maxCard

private theorem one_le_r {k B : ℕ} (hk : 2 ≤ k) (hB : 0 < B) : 1 ≤ r k B := by
  apply pinned_extremalBound hk [0] (by decide)
  · simpa using hB
  · intro a d hd terms
    have h₀ := terms 0 (by omega)
    have h₁ := terms 1 (by omega)
    simp at h₀ h₁
    omega

/-- Logarithm of the reciprocal extremal density at a dyadic length. -/
noncomputable def deficit (k j : ℕ) : ℝ := Real.log ((2:ℝ)^j / r k (2^j))

theorem deficit_monotone {k : ℕ} (hk : 2 ≤ k) : Monotone (deficit k) := by
  apply monotone_nat_of_le_succ
  intro j
  have denom (i : ℕ) : 0 < (r k (2^i) : ℝ) := by
    exact_mod_cast (show 0 < r k (2^i) from one_le_r hk (by positivity))
  have b := block_comparison (k:=k) (N:=2^(j+1)) (Q:=2) (B:=2^j) hk (by positivity)
    (by rw [pow_succ,Nat.mul_comm])
  apply Real.log_le_log (div_pos (by positivity) (denom j))
  apply (div_le_div_iff₀ (denom j) (denom (j+1))).mpr
  have br : (r k (2^(j+1)) : ℝ) ≤ 2 * (r k (2^j) : ℝ) := by exact_mod_cast b
  rw [pow_succ (2:ℝ),mul_assoc]
  exact mul_le_mul_of_nonneg_left br (by positivity)

theorem unrestricted_exceptional_count {k : ℕ} (hk : 2 ≤ k) (n w : ℕ) (e : ℝ) :
    (((range n).filter (fun i => e ≤ deficit k (i+w)-deficit k i)).card : ℝ) * e ≤
      (w:ℝ)*(deficit k (n+w)-deficit k 0) :=
  exceptional_windows _ (deficit_monotone hk) n w e

/-- Cross-multiplied comparison of an AP occupancy with the ambient extremal
density. Rounding only enters through Q and P, the numbers of blocks. -/
theorem local_density_comparison {k Q L P N U a d : ℕ} (hk : 2 ≤ k)
    (hL : 0 < L) (hN : 0 < N) (hU : U ≤ P*N) (hd : 0 < d)
    {A : Set ℕ} (hA : A.IsAPOfLengthFree k) (I : List ℕ) (hi : I.Nodup)
    (hI : ∀ x ∈ I, x < Q*L) (hm : ∀ x ∈ I, a+x*d ∈ A) :
    I.length * r k U ≤ (Q * r k L) * (P * r k N) :=
  Nat.mul_le_mul (ap_block_cover hk hL hd hA I hi hI hm) (block_comparison hk hN hU)

/-- Direct upper bound on one residue class of an unrestricted AP-free set.
Q and B can be chosen independently of the residue. -/
theorem residue_bound {k q Q B b : ℕ} (hk : 2 ≤ k) (hq : 0 < q) (hB : 0 < B)
    (A : Finset ℕ) (hf : (A : Set ℕ).IsAPOfLengthFree k)
    (hsize : ∀ x ∈ A, x < Q*B*q) :
    (A.filter (fun x => x%q=b)).card ≤ Q * r k B := by
  classical
  let S := A.filter (fun x => x%q=b)
  let I := S.toList.map (fun x => x/q)
  have spec {x} (hx : x ∈ S.toList) : x ∈ A ∧ x%q=b :=
    Finset.mem_filter.mp (Finset.mem_toList.mp hx)
  have hi : I.Nodup := by
    apply List.Nodup.map_on _ S.nodup_toList
    intro x hx y hy he
    have hex := Nat.mod_add_div x q
    have hey := Nat.mod_add_div y q
    rw [(spec hx).2,he] at hex
    rw [(spec hy).2] at hey
    omega
  have hb : ∀ i ∈ I, i < Q*B := by
    intro i hx
    obtain ⟨x,hxS,rfl⟩ := List.mem_map.mp hx
    exact (Nat.div_lt_iff_lt_mul hq).mpr (hsize x (spec hxS).1)
  have hm : ∀ i ∈ I, b+i*q ∈ (A : Set ℕ) := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
    have he : b+x/q*q=x := by
      rw [← (spec hx).2, Nat.mul_comm (x/q),Nat.mod_add_div]
    rw [he]
    exact (spec hx).1
  simpa [I,S] using ap_block_cover hk hB hq hf I hi hb hm

/-- A nonconstant midpoint identity detects precisely a nonconstant 3-AP. -/
private theorem midpoint_iff (A : ℕ → Prop) :
    APFree 3 A ↔ ∀ x y z, A x → A y → A z → x+z=y+y → x=y := by
  constructor
  · intro hf x y z hx hy hz he
    by_cases h : x=y
    · exact h
    exfalso
    by_cases hxy : x<y
    · apply hf x (y-x) (by omega)
      intro i hi
      have hc : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases hc with rfl | rfl | rfl
      · simpa using hx
      · rw [show x+1*(y-x)=y by omega]; exact hy
      · simpa [show x+2*(y-x)=z by omega] using hz
    · apply hf z (y-z) (by omega)
      intro i hi
      have hc : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases hc with rfl | rfl | rfl
      · simpa using hz
      · rw [show z+1*(y-z)=y by omega]; exact hy
      · simpa [show z+2*(y-z)=x by omega] using hx
  · intro H a d hd hh
    have he := H _ _ _ (hh 0 (by decide)) (hh 1 (by decide)) (hh 2 (by decide)) (by omega)
    omega

/-- Exact compatibility of unrestricted even and odd fibres. These two
cross constraints are invisible to inequalities involving cardinalities alone. -/
theorem parity_compatibility (A : ℕ → Prop) :
    let E := fun x => A (2*x)
    let O := fun x => A (2*x+1)
    APFree 3 A ↔ APFree 3 E ∧ APFree 3 O ∧
      (∀ i j t, E i → E j → O t → i+j ≠ 2*t+1) ∧
      (∀ i j t, O i → O j → E t → i+j+1 ≠ 2*t) := by
  dsimp only
  constructor
  · intro h
    have hm := (midpoint_iff A).mp h
    refine ⟨affine_preimage_free (offset:=0) (scale:=2) h (by decide)
      (fun x hx => by simpa [Nat.mul_comm] using hx),
      affine_preimage_free (offset:=1) (scale:=2) h (by decide)
      (fun x hx => by simpa [Nat.mul_comm,Nat.add_comm] using hx), ?_, ?_⟩
    · intro i j t hi hj ht he
      have := hm _ _ _ hi ht hj (by omega)
      omega
    · intro i j t hi hj ht he
      have := hm _ _ _ hi ht hj (by omega)
      omega
  · rintro ⟨hE,hO,hEO,hOE⟩
    rw [midpoint_iff]
    intro x y z hx hy hz he
    have digit (v : ℕ) : v=2*(v/2) ∨ v=2*(v/2)+1 := by omega
    rcases digit x with ex | ex <;> rcases digit y with ey | ey
    · have ez : z=2*(z/2) := by omega
      have h := (midpoint_iff _).mp hE (x/2) (y/2) (z/2) (ex ▸ hx) (ey ▸ hy) (ez ▸ hz) (by omega)
      omega
    · have ez : z=2*(z/2) := by omega
      exact False.elim (hEO _ _ _ (ex ▸ hx) (ez ▸ hz) (ey ▸ hy) (by omega))
    · have ez : z=2*(z/2)+1 := by omega
      exact False.elim (hOE _ _ _ (ex ▸ hx) (ez ▸ hz) (ey ▸ hy) (by omega))
    · have ez : z=2*(z/2)+1 := by omega
      have h := (midpoint_iff _).mp hO (x/2) (y/2) (z/2) (ex ▸ hx) (ey ▸ hy) (ez ▸ hz) (by omega)
      omega

end ScaleWindows

/-! An exact obstruction to recursive choices of extremisers on parity
classes. The two classes in [0,22) each have length 11. If one contains
six points of a 3-AP-free set, the other contains at most two. But nine
points are attainable in [0,22). See the companion note for the uniform
scale estimates. All finite checks here use kernel reduction. -/
namespace Parity22
open DigitProof

private def hit (xs : List ℕ) := xs.any fun x => xs.any fun y => decide (x<y) && xs.contains (2*y-x)

private theorem hit_impossible {A : ℕ → Prop} (hf : APFree 3 A) {xs : List ℕ}
    (hm : ∀ x ∈ xs, A x) (hh : hit xs = true) : False := by
  obtain ⟨x,hx,y,hy,hl,hz⟩ : ∃ x ∈ xs, ∃ y ∈ xs, x<y ∧ 2*y-x ∈ xs := by
    simpa [hit] using hh
  apply hf x (y-x) (by omega)
  intro i hi
  have : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases this with rfl | rfl | rfl
  · simpa using hm _ hx
  · rw [show x+1*(y-x)=y by omega]; exact hm _ hy
  · rw [show x+2*(y-x)=2*y-x by omega]; exact hm _ hz

private def joined (p : ℕ) (e o : List ℕ) :=
  (e.map fun x => 2*x+p) ++ (o.map fun x => 2*x+(1-p))

private def check (p : ℕ) :=
  ((List.range 11).sublistsLen 6).all fun e => hit e ||
    ((List.range 11).sublistsLen 3).all fun o => hit (joined p e o)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem checked : check 0 = true ∧ check 1 = true := by decide

/-- Any 6+3 configuration in these two fibres contains a nonconstant 3-AP. -/
theorem no_six_three {p : ℕ} (hp : p≤1) {A : ℕ → Prop} (hf : APFree 3 A)
    (e o : List ℕ) (he : e.Sublist (List.range 11)) (ho : o.Sublist (List.range 11))
    (hle : 6 ≤ e.length) (hlo : 3 ≤ o.length)
    (hm : ∀ x ∈ e, A (2*x+p)) (hn : ∀ x ∈ o, A (2*x+(1-p))) : False := by
  have hc : check p = true := by
    have : p=0 ∨ p=1 := by omega
    rcases this with rfl | rfl
    · exact checked.1
    · exact checked.2
  have subE := List.take_sublist 6 e
  have subO := List.take_sublist 3 o
  have row := List.all_eq_true.mp hc (e.take 6)
    (List.mem_sublistsLen.mpr ⟨subE.trans he, by simp [Nat.min_eq_left hle]⟩)
  rcases Bool.or_eq_true_iff.mp row with bad | rest
  · apply hit_impossible (A:=fun x => A (2*x+p)) _ (fun x hx => hm x (subE.subset hx)) bad
    exact affine_preimage_free (offset:=p) (scale:=2) hf (by decide)
      (fun x hx => by simpa [Nat.mul_comm,Nat.add_comm] using hx)
  · have bad := List.all_eq_true.mp rest (o.take 3)
      (List.mem_sublistsLen.mpr ⟨subO.trans ho, by simp [Nat.min_eq_left hlo]⟩)
    apply hit_impossible hf _ bad
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      exact hm v (subE.subset hv)
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      exact hn v (subO.subset hv)
set_option maxRecDepth 100000 in
private theorem seven_hit : ((List.range 11).sublistsLen 7).all hit = true := by decide

private theorem six_cap {A : ℕ → Prop} (hf : APFree 3 A) (e : List ℕ)
    (he : e.Sublist (List.range 11)) (hm : ∀ x ∈ e, A x) : e.length ≤ 6 := by
  apply Nat.le_of_not_lt
  intro many
  have sub := List.take_sublist 7 e
  have bad := List.all_eq_true.mp seven_hit (e.take 7)
    (List.mem_sublistsLen.mpr ⟨sub.trans he, by simp [Nat.min_eq_left many]⟩)
  exact hit_impossible hf (fun x hx => hm x (sub.subset hx)) bad

/-- At least nine accepted values force both fibres to miss six. -/
theorem both_fibres_suboptimal {A : ℕ → Prop} (hf : APFree 3 A) (e o : List ℕ)
    (he : e.Sublist (List.range 11)) (ho : o.Sublist (List.range 11))
    (hm : ∀ x ∈ e, A (2*x)) (hn : ∀ x ∈ o, A (2*x+1)) (big : 9 ≤ e.length+o.length) :
    e.length ≤ 5 ∧ o.length ≤ 5 := by
  have ecap := six_cap (A:=fun x => A (2*x))
    (affine_preimage_free (offset:=0) (scale:=2) hf (by decide)
      (fun x hx => by simpa [Nat.mul_comm] using hx)) e he hm
  have ocap := six_cap (A:=fun x => A (2*x+1))
    (affine_preimage_free (offset:=1) (scale:=2) hf (by decide)
      (fun x hx => by simpa [Nat.mul_comm,Nat.add_comm] using hx)) o ho hn
  constructor
  · apply Nat.le_of_not_lt
    intro many
    exact no_six_three (p:=0) (by decide) hf e o he ho many (by omega)
      (fun x h => by simpa using hm x h) hn
  · apply Nat.le_of_not_lt
    intro many
    exact no_six_three (p:=1) (by decide) hf o e ho he many (by omega) hn
      (fun x h => by simpa using hm x h)

private def w11 : List ℕ := [0,1,3,4,9,10]
private def w22 : List ℕ := [0,1,3,4,9,13,16,20,21]

theorem attainable_sizes :
    6 ≤ Set.IsAPOfLengthFree.maxCard 3 11 ∧ 9 ≤ Set.IsAPOfLengthFree.maxCard 3 22 := by
  constructor
  · apply pinned_extremalBound (by decide : 2 ≤ 3) w11 (by decide)
    · intro x hx; simp [w11] at hx; omega
    · intro a d hd h
      have h₀ := h 0 (by decide)
      have h₁ := h 1 (by decide)
      have h₂ := h 2 (by decide)
      simp [w11] at h₀ h₁ h₂
      omega
  · apply pinned_extremalBound (by decide : 2 ≤ 3) w22 (by decide)
    · intro x hx; simp [w22] at hx; omega
    · intro a d hd h
      have h₀ := h 0 (by decide)
      have h₁ := h 1 (by decide)
      have h₂ := h 2 (by decide)
      simp [w22] at h₀ h₁ h₂
      omega

end Parity22
