import sympy as sp
exec(open('genbranch.py').read().split("names={}")[0])
t,cw=sp.symbols('t cw')
def int2(e):
  e=sp.expand(e); a=e.coeff(w,0); b=e.coeff(w,1)
  assert a.q==1 and b.q==1, e
  return int(a),int(b)
six={k:int2(6*v) for k,v in s.items()}
k9=int2(9*k0)
def P(ab): return ab[0]+ab[1]*cw
u={k:1-P(six[k])*t for k in s}
D9=P(k9)*u['z0']*u['zr']; G9=54*t; E=u['q1']*u['q2']; Nn=cw**2*u['b1']*u['b2']
expr=sp.expand((D9**2+G9*D9+G9**2)*(E**2+Nn*E+Nn**2)-G9*D9*Nn*E)
q,r=sp.div(sp.Poly(expr,cw),sp.Poly(cw**2+cw+1,cw))
assert r.is_zero
terms=[]
for (i,j),cc in sp.Poly(sp.expand(q.as_expr()),t,cw).terms():
  terms.append("(%d : PK) * Gt ^ %d * C om ^ %d"%(int(cc),i,j))
open('Kcof2.txt','w').write(" + ".join(terms))
names={'z0':'s_z0','zr':'s_zr','b1':'s_b1','b2':'s_b2','q1':'s_q1','q2':'s_q2'}
lines=[]
for k,(a,b) in six.items():
  lines.append("  have h_%s : C %s * Gb = ((%d : PK) + (%d : PK) * C om) * Gt := by\n    rw [hG6, ← mul_assoc, ← map_ofNat C 6, ← map_mul, show %s * 6 = (%d : KK) + (%d : KK) * om by simp only [%s]; ring]\n    simp [map_add, map_mul, map_intCast]"%(k,names[k],a,b,names[k],a,b,names[k]))
lines.append("  have h_k9 : (9 : PK) * C k0 = ((%d : PK) + (%d : PK) * C om) := by\n    rw [← map_ofNat C 9, ← map_mul, show (9 : KK) * k0 = (%d : KK) + (%d : KK) * om by simp only [k0]; ring]\n    simp [map_add, map_mul, map_intCast]"%(k9[0],k9[1],k9[0],k9[1]))
open('Khyp.txt','w').write("\n".join(lines))
print(six,k9)
