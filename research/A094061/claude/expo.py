# exponents c(h,k) with K = prod (1 - x^h y^k)^{c(h,k)}
import sys
from math import gcd
from fractions import Fraction
N=int(sys.argv[1])
# K coefficients
T=[1,1,1]
K={}
for i in range(3):
  for j in range(3):
    K[(i,j)]=K.get((i,j),0)+T[i]*T[j]
K[(1,1)]-=1
# compute log K via: lam = x K_x / K  (integer series), up to degree N in each var
# Kinv
import numpy as np
def mul(A,B):
  C=[[0]*(N+1) for _ in range(N+1)]
  for (i,j),a in A.items():
    for u in range(N+1-i):
      Bu=B[u]
      Cr=C[i+u]
      for v in range(N+1-j):
        Cr[j+v]+=a*Bu[v]
  return C
# inverse of K: solve K*I=1
I=[[0]*(N+1) for _ in range(N+1)]
for s in range(0,2*N+1):
  for i in range(max(0,s-N),min(N,s)+1):
    j=s-i
    val=1 if (i,j)==(0,0) else 0
    acc=0
    for (a,b),c in K.items():
      if (a,b)!=(0,0) and a<=i and b<=j:
        acc+=c*I[i-a][j-b]
    I[i][j]=val-acc
xKx={(i,j):i*c for (i,j),c in K.items() if i>0}
yKy={(i,j):j*c for (i,j),c in K.items() if j>0}
LX=mul(xKx,I); LY=mul(yKy,I)
def ell(H,Kk):
  if H>0: return Fraction(LX[H][Kk],H)
  return Fraction(LY[H][Kk],Kk)
from sympy import mobius, divisors, factorint
c={}
for h in range(N+1):
  for k in range(N+1):
    if (h,k)==(0,0): continue
    g=gcd(h,k); h0,k0=h//g,k//g
    s=Fraction(0)
    for n in divisors(g):
      s+=mobius(g//n)*n*ell(n*h0,n*k0)
    cc=-s/g
    assert cc.denominator==1,(h,k,cc)
    c[(h,k)]=int(cc)
bad={}
for (h,k),v in c.items():
  g=gcd(h,k)
  for p,e in factorint(g).items():
    if v % p**e: bad.setdefault(p,[]).append((h,k,v))
print("checked up to",N)
for p in sorted(bad): print(p,len(bad[p]),bad[p][:5])
print("sample",[(hk,c[hk]) for hk in [(1,0),(2,0),(3,0),(1,1),(2,2),(3,3),(5,5),(5,0),(5,10),(7,7)] if hk in c])
