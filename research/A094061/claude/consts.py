import sympy as sp
m=sp.symbols('m'); r=sp.sqrt(-3)
X=r*(m+1/r)/(m*(m-r))
Yn=(1+r)*m**2+2*m+(1-r); Yd=(1-r)*m**2-2*m+(1+r)
m0=-1/r
k0=sp.simplify(1/sp.diff(X,m).subs(m,m0))
bz=sp.solve(Yn,m); bp=sp.solve(Yd,m)
B=[(b,1) for b in bz]+[(b,-1) for b in bp]
s=lambda a: 1/(a-m0)
def chk(z,name):
  z=sp.nsimplify(sp.simplify(z)); zc=complex(sp.N(z))
  ok=abs(abs(zc)-1)<1e-12 and any(abs(zc**k-1)<1e-10 for k in range(1,13))
  print(name,sp.simplify(z),"root of unity:",ok)
print("kappa0",k0)
for b,n in B:
  chk((s(b)-s(0))*(s(b)-s(r))*k0/s(b),"c0b*crb/cb at b=%s"%sp.simplify(b))
chk(sp.prod([(s(b)-s(0))**n for b,n in B]),"prod_b c0b^nb")
chk(sp.prod([(s(b)-s(r))**n for b,n in B]),"prod_b crb^nb")
