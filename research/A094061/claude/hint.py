import random
from fractions import Fraction as Fr
N=120
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
def log1(a):
  l=lam(a); return [Fr(0)]+[l[i]/i for i in range(1,N+1)]
def phi(a,p):
  r=[Fr(0)]*(N+1)
  for i,x in enumerate(a):
    if i*p<=N: r[i*p]=x
  return r
def li2(f):  # f(0)=0
  r=[Fr(0)]*(N+1); pw=[Fr(1)]+[Fr(0)]*N
  for n in range(1,N+1):
    pw=mul(pw,f)
    if all(x==0 for x in pw): break
    for i in range(N+1): r[i]+=pw[i]/(n*n)
  return r
def v(fr,p):
  if fr==0: return 99
  a,b=fr.numerator,fr.denominator;e=0
  while a%p==0:a//=p;e+=1
  while b%p==0:b//=p;e-=1
  return e
random.seed(1)
for trial in range(4):
  u=[Fr(1)]+[Fr(random.randint(-3,3)) for _ in range(6)]+[Fr(0)]*(N-6)
  a=random.choice([1,2])
  f=[Fr(0)]*a+u[:N+1-a]    # f = z^a u
  for p in [5,7]:
    Uf=[x-y/p for x,y in zip(log1(u),phi(log1(u),p))]
    one_m_f=[Fr(1)-f[0]]+[-x for x in f[1:]]
    H=[x-y/(p*p)+w for x,y,w in zip(li2(f),phi(li2(f),p),mul(Uf,log1(one_m_f)))]
    bad=[n for n in range(N+1) if v(H[n],p)<0]
    print(trial,a,p,"nonintegral idx:",bad[:6])
