import sympy as sp
w=sp.symbols('w')
mod=w**2+w+1
r=2*w+1
def red(e):
  e=sp.together(sp.expand(e))
  n,d=sp.fraction(e)
  n=sp.Poly(sp.expand(n),w).rem(sp.Poly(mod,w)).as_expr()
  d=sp.Poly(sp.expand(d),w).rem(sp.Poly(mod,w)).as_expr()
  # invert d: d = a+bw ; inverse = conj/norm, conj(w)=w^2=-1-w
  a=d.coeff(w,0); b=d.coeff(w,1)
  conj=a+b*(-1-w); N=sp.expand(a*a-a*b+b*b)
  e2=sp.Poly(sp.expand(n*conj),w).rem(sp.Poly(mod,w)).as_expr()/N
  return sp.expand(e2)
m0=red(r/3)
pts={'z0':0,'zr':r,'b1':-1,'b2':1+w,'q1':1,'q2':w}
nb={'b1':1,'b2':1,'q1':-1,'q2':-1}
s={k:red(1/(v-m0)) for k,v in pts.items()}
k0=red(-2*r/9)
print("m0",m0,"kappa0",k0)
for k,v in s.items(): print("s_"+k,v)
c={};
for b in nb:
  c['c_'+b]=red(s[b]*k0); c['c0_'+b]=red((s[b]-s['z0'])*k0); c['cr_'+b]=red((s[b]-s['zr'])*k0)
for k,v in c.items(): print(k,v,"  inv",red(1/v))
for b in nb:
  print("zeta_"+b, red(c['c0_'+b]*c['cr_'+b]/c['c_'+b]))
print("prod c0^n", red(c['c0_b1']*c['c0_b2']/(c['c0_q1']*c['c0_q2'])))
print("prod cr^n", red(c['cr_b1']*c['cr_b2']/(c['cr_q1']*c['cr_q2'])))
# check Y and z identities symbolically in g
g=sp.symbols('g')
u={k:1-s[k]*g for k in pts}
zz=g/(k0*u['z0']*u['zr'])
Y=red(w**2)*u['b1']*u['b2']/(u['q1']*u['q2'])
K=(1+zz+zz**2)*(1+Y+Y**2)-zz*Y
num=sp.numer(sp.together(K))
print("K numerator mod w^2+w+1:", sp.Poly(sp.expand(num),w).rem(sp.Poly(mod,w)).as_expr()==0 or sp.simplify(sp.Poly(sp.expand(num),w).rem(sp.Poly(mod,w)).as_expr()))
