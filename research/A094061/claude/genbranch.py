import sympy as sp
exec(open('omconst.py').read().split("# check Y")[0].replace("print(","(lambda *a,**k:None)("))
w=sp.symbols('w')
def ab(e):
  e=sp.expand(e); return (sp.Rational(e.coeff(w,0)), sp.Rational(e.coeff(w,1)))
def lit(q):
  q=sp.Rational(q)
  if q.q==1: return "(%d : KK)"%q.p if q.p>=0 else "(-%d : KK)"%(-q.p)
  return "(%d/%d : KK)"%(q.p,q.q) if q.p>=0 else "(-%d/%d : KK)"%(-q.p,q.q)
def klit(e):
  a,b=ab(e); return "(%s + %s * om)"%(lit(a),lit(b))
def cof(lhs,rhs):
  # lhs-rhs polynomial in w (expanded, as polynomial not reduced) ; quotient by w^2+w+1
  P=sp.Poly(sp.expand(lhs-rhs),w); q,rm=sp.div(P,sp.Poly(mod,w))
  assert rm.is_zero, (lhs,rhs,rm)
  qe=q.as_expr()
  a=sp.expand(qe).coeff(w,0); b=sp.expand(qe).coeff(w,1); c2=sp.expand(qe).coeff(w,2)
  terms=[]
  for k,cc in [(0,a),(1,b),(2,c2)]:
    if cc!=0: terms.append("%s * om ^ %d"%(lit(cc),k))
  return " + ".join(terms) if terms else "(0 : KK)"
names={}
L=[]
L.append("""import A094061Dev.Consts

/-!
Explicit constants in `ℚ(ω)` for the branch decomposition (generated; see research/A094061/claude/genbranch.py).
-/

namespace A094061

open PowerSeries

lemma pint_den {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : ℚ) (h : q.den ∣ 36) : pint p q := by
  intro hpd
  have h1 : p ∣ 2 ^ 2 * 3 ^ 2 := by have := dvd_trans hpd h; norm_num at this ⊢; exact this
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega

lemma OI_lit {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℚ) (ha : a.den ∣ 36) (hb : b.den ∣ 36) :
    OI p ((a : KK) + (b : KK) * om) :=
  ⟨a, b, pint_den hp hp5 a ha, pint_den hp hp5 b hb, by simp [rr]⟩
""")
allc={'k0':k0}
for k,v in s.items(): allc['s_'+k]=v
for k,v in c.items(): allc[k.replace('c0_','c0').replace('cr_','cr').replace('c_','c')]=v
for nm,v in allc.items():
  L.append("noncomputable def %s : KK := %s\n"%(nm,klit(v)))
# OI lemmas and inverse lemmas
for nm,v in allc.items():
  a,b=ab(v)
  L.append("""lemma OI_%s {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p %s := by
  have := OI_lit hp hp5 (%s) (%s) (by norm_num) (by norm_num); simpa [%s] using this
"""%(nm,nm,sp.sstr(a),sp.sstr(b),nm))
for nm,v in allc.items():
  if nm.startswith('c') or nm=='k0':
    iv=red(1/v); ai,bi=ab(iv)
    L.append("""lemma %s_mul_inv : %s * %s = 1 := by
  rw [%s]; linear_combination (%s) * om_rel
"""%(nm,nm,klit(iv),nm,cof(v*iv,1)))
    L.append("""lemma %s_ne : %s ≠ 0 := fun h => by have := %s_mul_inv; rw [h, zero_mul] at this; exact zero_ne_one this
"""%(nm,nm,nm))
    L.append("""lemma OI_%s_inv {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OI p %s⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right %s_mul_inv]
  have := OI_lit hp hp5 (%s) (%s) (by norm_num) (by norm_num); simpa using this
"""%(nm,nm,nm,sp.sstr(ai),sp.sstr(bi)))
# defining relations
for b in nb:
  L.append("""lemma c%s_eq : c%s = s_%s * k0 := by
  simp only [c%s, s_%s, k0]; linear_combination (%s) * om_rel
"""%(b,b,b,b,b,cof(c['c_'+b], s[b]*k0)))
  L.append("""lemma c0%s_eq : c0%s = (s_%s - s_z0) * k0 := by
  simp only [c0%s, s_%s, s_z0, k0]; linear_combination (%s) * om_rel
"""%(b,b,b,b,b,cof(c['c0_'+b], (s[b]-s['z0'])*k0)))
  L.append("""lemma cr%s_eq : cr%s = (s_%s - s_zr) * k0 := by
  simp only [cr%s, s_%s, s_zr, k0]; linear_combination (%s) * om_rel
"""%(b,b,b,b,b,cof(c['cr_'+b], (s[b]-s['zr'])*k0)))
# root of unity relations
zeta={}
for b in nb:
  z=red(c['c0_'+b]*c['cr_'+b]/c['c_'+b]); zeta[b]=z
  zl = "om" if sp.expand(z-w)==0 else "(-1 - om)"
  L.append("""lemma root_%s : c0%s * cr%s = %s * c%s := by
  simp only [c0%s, cr%s, c%s]; linear_combination (%s) * om_rel
"""%(b,b,b,zl,b,b,b,b,cof(c['c0_'+b]*c['cr_'+b], z*c['c_'+b])))
z0=red(c['c0_b1']*c['c0_b2']/(c['c0_q1']*c['c0_q2']))
zr=red(c['cr_b1']*c['cr_b2']/(c['cr_q1']*c['cr_q2']))
def zlit(z):
  if sp.expand(z-1)==0: return "1"
  if sp.expand(z-w)==0: return "om"
  return "(-1 - om)"
L.append("""lemma root_0 : c0b1 * c0b2 = %s * (c0q1 * c0q2) := by
  simp only [c0b1, c0b2, c0q1, c0q2]; linear_combination (%s) * om_rel
"""%(zlit(z0), cof(c['c0_b1']*c['c0_b2'], z0*c['c0_q1']*c['c0_q2'])))
L.append("""lemma root_r : crb1 * crb2 = %s * (crq1 * crq2) := by
  simp only [crb1, crb2, crq1, crq2]; linear_combination (%s) * om_rel
"""%(zlit(zr), cof(c['cr_b1']*c['cr_b2'], zr*c['cr_q1']*c['cr_q2'])))
L.append("\nend A094061\n")
open('/home/user/open-math-agents/research/A094061/lean/BConst.lean','w').write("\n".join(L))
print("zetas",zeta,z0,zr)
