from fractions import Fraction as Fr
N=200
def mul(a,b):
  c=[Fr(0)]*(N+1)
  for i,x in enumerate(a):
    if x:
      for j in range(N+1-i):
        if b[j]: c[i+j]+=x*b[j]
  return c
def inv(a):
  r=[Fr(0)]*(N+1); r[0]=1/a[0]
  for n in range(1,N+1):
    r[n]=-sum(a[k]*r[n-k] for k in range(1,n+1))/a[0]
  return r
def D(a): return [i*x for i,x in enumerate(a)]
def lam(a): return mul(D(a),inv(a))
def log(a):  # a[0]=1
  l=lam(a); return [Fr(0)]+[l[i]/i for i in range(1,N+1)]
def phi(a,p):
  r=[Fr(0)]*(N+1)
  for i,x in enumerate(a):
    if i*p<=N: r[i*p]=x
  return r
def U(a,p):
  la=log(a); return [la[i]-phi(la,p)[i]/p for i in range(N+1)]
def E(f,g,p):
  Uf=U(f,p);Ug=U(g,p)
  return [x-y for x,y in zip(mul(Uf,lam(g)), mul(Ug,phi(lam(f),p)))]
def v(fr,p):
  if fr==0: return 99
  a,b=fr.numerator,fr.denominator;e=0
  while a%p==0:a//=p;e+=1
  while b%p==0:b//=p;e-=1
  return e
def vi(n,p):
  e=0
  while n%p==0:n//=p;e+=1
  return e
def inDR(s,p): return [n for n in range(1,N+1) if v(s[n],p)<vi(n,p)]
def poly(cs): return [Fr(c) for c in cs]+[Fr(0)]*(N+1-len(cs))
onepz=poly([1,1]); T=poly([1,1,1]); onemz=poly([1,-1])
for p in [5,7,11]:
  print(p,"E(1+z,T):",inDR(E(onepz,T,p),p)[:8]," E(1+z,1-z):",inDR(E(onepz,onemz,p),p)[:8], "const0", E(onepz,T,p)[0])
