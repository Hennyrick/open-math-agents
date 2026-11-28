import Erdos142ParityMass

/-! A face of the Boolean cube which meets the deleted set in at least one
vertex of each antipodal pair contains two deleted vertices differing in
all but at most one of the free coordinates. Coordinates below number
the free positions of the face. -/
namespace ParityFace
abbrev Vertex (j : ℕ) := Fin j → Bool
def opposite {j} (u : Vertex j) : Vertex j := fun i => !(u i)
private def path {j} (u : Vertex j) (k : ℕ) : Vertex j :=
  fun i => if i.val < k then !(u i) else u i

private theorem path_zero {j} (u : Vertex j) : path u 0 = u := by
  funext i
  simp [path]

private theorem path_last {j} (u : Vertex j) : path u j = opposite u := by
  funext i
  simp [path,opposite,i.isLt]

private theorem transition (P : ℕ → Prop) {j : ℕ} (h0 : P 0) (hj : ¬P j) :
    ∃ k, k<j ∧ P k ∧ ¬P (k+1) := by
  induction j with
  | zero => exact (hj h0).elim
  | succ n ih =>
    by_cases hn : P n
    · exact ⟨n,by omega,hn,hj⟩
    · obtain ⟨k,hk,hp,hq⟩ := ih hn
      exact ⟨k,by omega,hp,hq⟩

/-- A gap of zero or one coordinate suffices. The two vertices may
coincide when the face is an edge. -/
theorem antipodal_or_near {j : ℕ} (D : Vertex j → Prop)
    (hit : ∀ u, D u ∨ D (opposite u)) :
    ∃ a b, D a ∧ D b ∧
      ((∀ i, b i = !(a i)) ∨
       ∃ s : Fin j, b s = a s ∧ ∀ i, i ≠ s → b i = !(a i)) := by
  classical
  let z : Vertex j := fun _ => false
  obtain ⟨u,hu⟩ : ∃ u, D u := (hit z).elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
  by_cases ho : D (opposite u)
  · exact ⟨u,opposite u,hu,ho,Or.inl (fun _ => rfl)⟩
  obtain ⟨k,hk,hp,hq⟩ := transition (j := j) (fun t => D (path u t))
    (by simpa only [path_zero] using hu) (by simpa only [path_last] using ho)
  refine ⟨path u k,opposite (path u (k+1)),hp,(hit _).resolve_left hq,Or.inr ?_⟩
  refine ⟨⟨k,hk⟩,?_,?_⟩
  · simp [opposite,path]
  · intro i hi
    have ne : i.val ≠ k := fun h => hi (Fin.ext h)
    by_cases lo : i.val < k
    · simp [opposite,path,lo,show i.val < k+1 by omega]
    · simp [opposite,path,lo,show ¬i.val < k+1 by omega]

end ParityFace
namespace ParityFace
private def oddResidues : List ℕ := [11,19,20,23,47]
private def allResidues : List ℕ :=
  [0,2,6,8,18,20,24,26,54,56,60,62,72,74,78,80,11,19,23,47]

/-- For the alternating one-deletion construction with low bits 1,0,1,0,
the endpoint 3^m can be adjoined for every m >= 4. The hypotheses are
its residue signature, and hold for any set with that signature. -/
theorem extend_at_multiple_of_81 (A : ℕ → Prop) (q : ℕ)
    (hf : DigitProof.APFree 3 A) (below : ∀ x, A x → x<q)
    (hq : q%81=0) (odd : q%2=1)
    (endpoints : ∀ x, A x → x%2=1 → x%81 ∈ oddResidues)
    (middles : ∀ x, A x → x%81 ∈ allResidues) :
    DigitProof.APFree 3 (fun x => A x ∨ x=q) := by
  intro a d hd hall
  have h0 : A a ∨ a=q := by simpa using hall 0 (by decide)
  have h1 : A (a+d) ∨ a+d=q := by simpa using hall 1 (by decide)
  have h2 : A (a+2*d) ∨ a+2*d=q := by simpa using hall 2 (by decide)
  have ub : a+2*d ≤ q := h2.elim (fun h => (below _ h).le) (fun h => h.le)
  have ha : A a := h0.resolve_right (by omega)
  have hb : A (a+d) := h1.resolve_right (by omega)
  rcases h2 with hc | hc
  · apply hf _ _ hd
    intro i hi
    have : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases this with rfl|rfl|rfl
    · simpa using ha
    · simpa using hb
    · exact hc
  · have hcert : oddResidues.all (fun r => allResidues.all
        (fun s => decide (r ≠ (2*s)%81))) = true := by decide
    have ha' := endpoints a ha (by omega)
    have hb' := middles (a+d) hb
    have bad := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hcert _ ha') _ hb')
    exact bad (by omega)

end ParityFace
