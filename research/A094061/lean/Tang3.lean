import A094061Dev.Tang2

/-!
The tangential Steinberg lemma, part 2: truncation and integrality.
-/

namespace A094061

open PowerSeries

lemma TQ_mono {K : ℕ} {f g : PK} (h : TQ (K + 1) f g) : TQ K f g :=
  (pow_dvd_pow X (by omega)).trans h

section claimAC
variable {p : ℕ} (hp : p.Prime) (h3 : ¬ 3 ∣ p) (κ Uc : KK) (u : PK) (hu1 : constantCoeff u = 1)

/-- The Steinberg pairing `E(f, 1 - f)` for `f = κ z u`, with `U(κ) = Uc`. -/
noncomputable def Epair : PK :=
  (C Uc + UU hp h3 u) * ld1 (1 - ff κ u) - UU hp h3 (1 - ff κ u) * (1 + phi1 p hp.ne_zero h3 (ld1 u))

include hu1

lemma Epair_eq : Epair hp h3 κ Uc u = (C Uc + UU hp h3 u) * (-(ell u * (thk 2 Li2).subst (ff κ u)))
    - (-(thk 1 Li2).subst (ff κ u) + (p : KK)⁻¹ • (thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))))
      * (ell u - E1 (UU hp h3 u)) := by
  rw [Epair, ld1_one_sub_ff hp κ u hu1, UU_one_sub_ff hp h3 κ u hu1, ← phi_ell hp h3 u, ell, map_add,
    map_one]

lemma taylor_SS (N : ℕ) : TQ (N + 1) ((thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))))
    (SS hp h3 κ u N) := by
  have ht : constantCoeff (lg (thq hp h3 u)) = 0 := const_lg _
  refine (taylor (thk 1 Li2) (const_ww h3 κ u hp.ne_zero) ht (N + 1)).trans ?_
  rw [SS]
  apply TQ_of_coeff
  intro n _
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lg_thq hp h3 u hu1, thk_add, RR, neg_pow, smul_pow, smul_eq_C_mul, aa]
  rw [show k + 1 = 1 + k by ring]
  simp only [map_mul, map_pow, map_neg, map_one, div_eq_mul_inv, map_natCast]
  ring

lemma TQ_E1H (N : ℕ) : TQ N (E1 (H1 h3 κ Uc u + H2 hp h3 κ u + H3 hp h3 κ u N))
    (Epair hp h3 κ Uc u) := by
  rw [main_identity hp h3 κ Uc u hu1 N, Epair_eq hp h3 κ Uc u hu1]
  have hU0 : constantCoeff (UU hp h3 u) = 0 := const_UU hp h3 u
  have hb : TQ N (C (aa p (N + 1) / p) * UU hp h3 u ^ (N + 1) * E1 (UU hp h3 u) * RR h3 κ u (N + 2)) 0 := by
    have := (TQ_zero_of_pow hU0 (K := N) (d := N + 1) (by omega))
    have h2 := (TQ.refl N (C (aa p (N + 1) / p))).mul (this.mul (TQ.refl N (E1 (UU hp h3 u) * RR h3 κ u (N + 2))))
    simpa [mul_assoc] using h2
  have ht := TQ_mono (taylor_SS hp h3 κ u hu1 N)
  have hE : TQ N (Ep' hp h3 κ Uc u N) ((C Uc + UU hp h3 u) * (-(ell u * (thk 2 Li2).subst (ff κ u)))
      - (-(thk 1 Li2).subst (ff κ u) + (p : KK)⁻¹ • (thk 1 Li2).subst (ww h3 κ u * ex1 (lg (thq hp h3 u))))
        * (ell u - E1 (UU hp h3 u))) := by
    rw [Ep', smul_eq_C_mul]
    exact (TQ.refl _ _).sub (((TQ.refl _ _).add ((TQ.refl _ _).mul ht.symm)).mul (TQ.refl _ _))
  have := (hE.sub hb)
  simpa using this

end claimAC

end A094061
