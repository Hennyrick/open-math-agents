import Erdos142DigitBounds

namespace ParityCarry
open DigitProof

theorem zero_layer (m : ℕ) : CantorLayer m 0 := by
  induction m with
  | zero => rfl
  | succ m h => exact ⟨0,h,0,by decide,by simp⟩

private theorem extend {m a : ℕ} (h : CantorLayer m a) (e : ℕ) (he : e<2) :
    CantorLayer (m+1) (a*3+e) := ⟨a,h,e,he,rfl⟩

/-- Every m-digit ternary integer is a sum of two {0,1}-digit integers. -/
theorem full_sum (m s : ℕ) (hs : s<3^m) :
    ∃ a b, CantorLayer m a ∧ CantorLayer m b ∧ a+b=s := by
  induction m generalizing s with
  | zero =>
    exact ⟨0,0,rfl,rfl,by simpa using Nat.eq_zero_of_le_zero (show s≤0 by simpa using hs) |>.symm⟩
  | succ m ih =>
    rw [pow_succ] at hs
    obtain ⟨a,b,ha,hb,hsum⟩ := ih (s/3) (by omega)
    refine ⟨a*3+(s%3)/2,b*3+(s%3+1)/2,extend ha _ (by omega),extend hb _ (by omega),by omega⟩

theorem nonzero_sum {m s : ℕ} (hs : s<3^m) (positive : 0<s)
    (hpow : ∀ i, s ≠ 3^i) :
    ∃ a b, CantorLayer m a ∧ CantorLayer m b ∧ 0<a ∧ 0<b ∧ a+b=s := by
  induction m generalizing s with
  | zero => simp at hs; omega
  | succ m ih =>
    rw [pow_succ] at hs
    have hq : s/3 < 3^m := by omega
    by_cases h0 : s%3=0
    · have eq : s=(s/3)*3 := by omega
      obtain ⟨a,b,ha,hb,pa,pb,h⟩ := ih hq (by omega) (by
        intro i e; apply hpow (i+1); rw [pow_succ,← e]; exact eq)
      exact ⟨_,_,extend ha 0 (by decide),extend hb 0 (by decide),by omega,by omega,by omega⟩
    obtain ⟨a,b,ha,hb,h⟩ := full_sum m _ hq
    by_cases h2 : s%3=2
    · exact ⟨_,_,extend ha 1 (by decide),extend hb 1 (by decide),by omega,by omega,by omega⟩
    have ne : s ≠ 1 := hpow 0
    by_cases pa : 0<a
    · exact ⟨_,_,extend ha 0 (by decide),extend hb 1 (by decide),by omega,by omega,by omega⟩
    · exact ⟨_,_,extend ha 1 (by decide),extend hb 0 (by decide),by omega,by omega,by omega⟩

/-- The only representations of a power of 3 as a sum from the layer have
a zero summand. -/
theorem power_sum {m a b : ℕ} (ha : CantorLayer m a) (hb : CantorLayer m b)
    (i : ℕ) (hs : a+b=3^i) : a=0 ∨ b=0 := by
  induction m generalizing i a b with
  | zero => exact Or.inl ha
  | succ m ih =>
    obtain ⟨x,hx,e,he,rfl⟩ := ha
    obtain ⟨y,hy,f,hf,rfl⟩ := hb
    cases i with
    | zero => simp at hs; omega
    | succ i =>
      rw [pow_succ] at hs
      have h := ih hx hy i (by omega)
      omega

/-- Exact set of odd midpoint positions liberated by deleting zero,
strictly below the right endpoint 3^m. -/
theorem odd_midpoint_holes {m s : ℕ} (hs : s<3^m) (odd : s%2=1) :
    (¬ ∃ a b, CantorLayer m a ∧ CantorLayer m b ∧ 0<a ∧ 0<b ∧ a+b=s) ↔
      ∃ i, s=3^i := by
  constructor
  · intro h; by_contra! hn; exact h (nonzero_sum hs (by omega) hn)
  · rintro ⟨i,hi⟩ ⟨a,b,ha,hb,pa,pb,h⟩
    have := power_sum ha hb i (h.trans hi)
    omega


private def ternary (x : ℕ) : Prop := ∃ m, CantorLayer m x

private theorem down {x : ℕ} (h : ternary x) : ternary (x/3) := by
  obtain ⟨m,hm⟩ := h
  cases m with
  | zero => exact ⟨0,by change x=0 at hm; change x/3=0; omega⟩
  | succ m =>
    obtain ⟨v,hv,d,hd,rfl⟩ := hm
    exact ⟨m,by rwa [show (v*3+d)/3=v by omega]⟩

private theorem digit {x : ℕ} (h : ternary x) : x%3<2 := by
  obtain ⟨m,h⟩ := h
  cases m with
  | zero => change x=0 at h; omega
  | succ m => obtain ⟨v,_,d,hd,rfl⟩ := h; omega

/-- The only pair of distinct odd powers of 3 whose midpoint is twice
a {0,1}-ternary integer has adjacent exponents. -/
theorem conflict_only_adjacent {m c : ℕ} (hc : CantorLayer m c) (i gap : ℕ)
    (h : 4*c = 3^i + 3^(i+(gap+1))) : gap=0 := by
  have aux (i : ℕ) : ∀ c : ℕ, ternary c → 4*c=3^i+3^(i+(gap+1)) → gap=0 := by
    induction i with
    | zero =>
      intro c ht eqn
      cases gap with
      | zero => rfl
      | succ j =>
        have hx := digit ht
        have hy := digit (down ht)
        simp only [zero_add,pow_zero] at eqn
        rw [pow_succ,pow_succ] at eqn
        omega
    | succ i ih =>
      intro c ht eqn
      rw [Nat.succ_add, pow_succ 3 (i+(gap+1)), pow_succ 3 i] at eqn
      apply ih (c/3) (down ht); omega
  exact aux i c ⟨m,hc⟩ h

private theorem power_mem (i m : ℕ) (hi : i<m) : CantorLayer m (3^i) := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero => exact ⟨0,zero_layer _,1,by decide,by simp⟩
    | succ i => exact ⟨3^i,ih i (by omega),0,by decide,by simp [pow_succ]⟩

private theorem bounded (m x : ℕ) (h : CantorLayer m x) : 2*x<3^m := by
  induction m generalizing x with
  | zero => change x=0 at h; simp [h]
  | succ m ih =>
    obtain ⟨y,hy,d,hd,rfl⟩ := h
    have := ih y hy
    rw [pow_succ]; omega

private theorem pow_odd (i : ℕ) : 3^i%2=1 := by
  induction i with
  | zero => decide
  | succ i ih => rw [pow_succ]; omega

/-- Put all positive doubled Cantor integers in the even fibre. Choose
odd points 3^i with indices from J in [0,m]. This union is 3-AP-free
exactly when J contains no two consecutive indices. -/
theorem path_criterion (m : ℕ) (J : ℕ → Prop) (hj : ∀ i, J i → i≤m) :
    let A := fun x => (∃ c, CantorLayer m c ∧ 0<c ∧ x=2*c) ∨ ∃ i, J i ∧ x=3^i
    APFree 3 A ↔ ∀ i, J i → ¬ J (i+1) := by
  dsimp only
  constructor
  · intro hf i h₀ h₁
    have lt : i<m := by have := hj _ h₁; omega
    have hpos : 0<3^i := by positivity
    apply hf (3^i) (3^i) hpos
    intro j h
    have : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases this with rfl|rfl|rfl
    · exact Or.inr ⟨i,h₀,by simp⟩
    · exact Or.inl ⟨3^i,power_mem i m lt,hpos,by omega⟩
    · exact Or.inr ⟨i+1,h₁,by rw [pow_succ]; omega⟩
  · intro independent a d hd hall
    have x := hall 0 (by decide)
    have y := hall 1 (by decide)
    have z := hall 2 (by decide)
    simp only [zero_mul,add_zero,one_mul] at x y z
    rcases x with ⟨u,hu,upu,ex⟩ | ⟨i,hi,ex⟩ <;>
      rcases z with ⟨v,hv,upv,ez⟩ | ⟨j,hj',ez⟩
    · rcases y with ⟨t,ht,ut,ey⟩ | ⟨i,hi,ey⟩
      · apply cantor_layer_apFree m u (t-u) (by omega)
        intro s hs
        have : s=0 ∨ s=1 ∨ s=2 := by omega
        rcases this with rfl|rfl|rfl
        · simpa using hu
        · rw [show u+1*(t-u)=t by omega]; exact ht
        · rw [show u+2*(t-u)=v by omega]; exact hv
      · have eq : u+v=3^i := by omega
        have := power_sum hu hv i eq; omega
    · have := pow_odd j; omega
    · have := pow_odd i; omega
    · have ord : i<j := by
        by_contra! bad
        have := Nat.pow_le_pow_right (by decide : 0<3) bad
        omega
      rcases y with ⟨t,ht,ut,ey⟩ | ⟨l,hl,ey⟩
      · let g := j-i-1
        have je : j=i+(g+1) := by dsimp [g]; omega
        have eq : 4*t=3^i+3^(i+(g+1)) := by rw [← je]; omega
        have := conflict_only_adjacent ht i g eq
        apply independent i hi
        simpa [show j=i+1 by omega] using hj'
      · apply cantor_layer_apFree (m+1) a d hd
        intro s hs
        have : s=0 ∨ s=1 ∨ s=2 := by omega
        rcases this with rfl|rfl|rfl
        · simpa [ex] using power_mem i (m+1) (by have := hj i hi; omega)
        · rw [one_mul,ey]; exact power_mem l _ (by have := hj l hl; omega)
        · rw [ez]; exact power_mem j _ (by have := hj j hj'; omega)

private theorem midpoints_forbidden {A : ℕ → Prop} (hf : APFree 3 A)
    {a b s : ℕ} (ha : A (2*a)) (hb : A (2*b)) (h : a+b=s) (neq : a ≠ b) : ¬ A s := by
  intro hs
  let lo := min a b
  let hi := max a b
  have order : lo < hi := by dsimp [lo,hi]; omega
  have eq : lo+hi=s := by dsimp [lo,hi]; omega
  have ends : A (2*lo) ∧ A (2*hi) := by
    by_cases hab : a≤b
    · simpa [lo,hi,min_eq_left hab,max_eq_right hab] using And.intro ha hb
    · have hba : b≤a := by omega
      simpa [lo,hi,min_eq_right hba,max_eq_left hba] using And.intro hb ha
  apply hf (2*lo) (hi-lo) (by omega)
  intro i hi'
  have : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases this with rfl|rfl|rfl
  · simpa using ends.1
  · rw [show 2*lo+1*(hi-lo)=s by omega]; exact hs
  · rw [show 2*lo+2*(hi-lo)=2*hi by omega]; exact ends.2

theorem odd_when_core_retained {A : ℕ → Prop} {m s : ℕ} (hf : APFree 3 A)
    (core : ∀ c, CantorLayer m c → A (2*c)) (hs : s≤3^m) (ho : s%2=1) (ha : A s) :
    s=3^m := by
  by_contra! ne
  obtain ⟨c,d,hc,hd,he⟩ := full_sum m s (by omega)
  exact midpoints_forbidden hf (core c hc) (core d hd) he (by omega) ha

theorem odd_when_zero_deleted {A : ℕ → Prop} {m s : ℕ} (hf : APFree 3 A)
    (core : ∀ c, CantorLayer m c → 0<c → A (2*c)) (hs : s≤3^m) (ho : s%2=1)
    (ha : A s) : ∃ i, s=3^i := by
  by_cases he : s=3^m
  · exact ⟨m,he⟩
  apply (odd_midpoint_holes (by omega : s<3^m) ho).mp
  rintro ⟨c,d,hc,hd,pc,pd,hsum⟩
  exact midpoints_forbidden hf (core c hc pc) (core d hd pd) hsum (by omega) ha

/-- Every occupied site outside the core and below its outer endpoint is
impossible when the core is intact, including sites of even parity. -/
theorem intact_core {A : ℕ → Prop} {m s : ℕ} (hf : APFree 3 A)
    (core : ∀ c, CantorLayer m c → A (2*c)) (hs : s<3^m) (ha : A s) :
    ∃ c, CantorLayer m c ∧ s=2*c := by
  obtain ⟨c,d,hc,hd,he⟩ := full_sum m s hs
  by_cases eq : c=d
  · exact ⟨c,hc,by omega⟩
  · exact False.elim (midpoints_forbidden hf (core c hc) (core d hd) he eq ha)

/-- Complete classification of the possible extra sites after deleting zero:
all are powers of three, including the outer endpoint. -/
theorem all_extras_after_zero {A : ℕ → Prop} {m s : ℕ} (hf : APFree 3 A)
    (h₀ : ¬ A 0) (core : ∀ c, CantorLayer m c → 0<c → A (2*c))
    (hs : s≤3^m) (ha : A s) :
    (∃ c, CantorLayer m c ∧ 0<c ∧ s=2*c) ∨ ∃ i, s=3^i := by
  by_cases power : ∃ i, s=3^i
  · exact Or.inr power
  · have notPower : ∀ i, s ≠ 3^i := fun i e => power ⟨i,e⟩
    have pos : 0<s := by by_contra! hh; exact h₀ ((show s=0 by omega) ▸ ha)
    have ne := notPower m
    obtain ⟨c,d,hc,hd,pc,pd,he⟩ := nonzero_sum (by omega : s<3^m) pos notPower
    by_cases eq : c=d
    · exact Or.inl ⟨c,hc,pc,by omega⟩
    · exact False.elim (midpoints_forbidden hf (core c hc pc) (core d hd pd) he eq ha)

/-- The published 47-point construction is independently checked here.
Taken from the 91-point entry of span 686 in Wróblewski's DATABASE.TXT,
restricting the listed points to [448,691] and translating by -448. -/
private def known47 : List ℕ := [0,5,6,9,11,20,21,23,27,28,30,38,52,57,58,61,63,72,73,75,79,80,82,90,156,161,162,165,167,176,177,179,183,184,186,194,208,213,214,217,219,228,229,231,235,236,238]

theorem unrestricted_47 : 47 ≤ Set.IsAPOfLengthFree.maxCard 3 244 := by
  apply pinned_extremalBound (by decide : 2 ≤ 3) known47 (by decide)
  · intro x hx; exact of_decide_eq_true (List.all_eq_true.mp (show known47.all (fun i => decide (i<244)) = true by decide) x hx)
  · have cert : known47.all (fun x => known47.all (fun y =>
        decide (¬(x<y ∧ (2*y-x) ∈ known47)))) = true := by decide
    intro a d hd hall
    have h₀ : a ∈ known47 := by simpa using hall 0 (by decide)
    have h₁ : a+d ∈ known47 := by simpa using hall 1 (by decide)
    have h₂ := hall 2 (by decide)
    have hbad := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert a h₀) (a+d) h₁)
    apply hbad ⟨by omega, ?_⟩
    rwa [show 2*(a+d)-a=a+2*d by omega]

end ParityCarry
