import sys
from fractions import Fraction as Fr
N=30
def zero(): return [[0]*(N+1) for _ in range(N+1)]
def mul(A,B):
  C=zero()
  for i in range(N+1):
    for j in range(N+1):
      a=A[i][j]
      if a==0: continue
      for u in range(N+1-i):
        Bu=B[u]; Cr=C[i+u]
        for v in range(N+1-j):
          if Bu[v]: Cr[j+v]+=a*Bu[v]
  return C
def inv(A):
  assert A[0][0] in (1,-1)
  I=zero(); c0=A[0][0]
  for s in range(2*N+1):
    for i in range(max(0,s-N),min(N,s)+1):
      j=s-i
      acc=1 if (i,j)==(0,0) else 0
      for a in range(i+1):
        for b in range(j+1):
          if (a,b)!=(0,0) and A[a][b]: acc-=A[a][b]*I[i-a][j-b]
      I[i][j]=acc*c0
  return I
def logco(F):
  # coefficients of log F (F(0)=1) as Fractions
  Fi=inv(F)
  xFx=zero(); yFy=zero()
  for i in range(N+1):
    for j in range(N+1):
      xFx[i][j]=i*F[i][j]; yFy[i][j]=j*F[i][j]
  LX=mul(xFx,Fi); LY=mul(yFy,Fi)
  l={}
  for i in range(N+1):
    for j in range(N+1):
      if i>0: l[(i,j)]=Fr(LX[i][j],i)
      elif j>0: l[(i,j)]=Fr(LY[i][j],j)
  return l
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
def test(F,name,ps=(5,7)):
  l=logco(F)
  res=[]
  for p in ps:
    bad=0
    for (h,k),c in l.items():
      d=c-(l[(h//p,k//p)]/p if h%p==0 and k%p==0 and (h//p,k//p)!=(0,0) else 0)
      m=min(vi(h,p) if h else 99, vi(k,p) if k else 99)
      if v(d,p)<m: bad+=1
    res.append((p,bad))
  print(name,res)
# sigma(x) series
def sig1(var):
  S=zero()
  # x/(1+x)^2 = sum (-1)^(n-1) n x^n
  for n in range(1,N+1):
    if var=='x': S[n][0]=(-1)**(n-1)*n
    else: S[0][n]=(-1)**(n-1)*n
  return S
sx=sig1('x'); ty=sig1('y')
one=zero(); one[0][0]=1
def pw(A,k):
  R=one
  for _ in range(k): R=mul(R,A)
  return R
def sub(A,B): return [[A[i][j]-B[i][j] for j in range(N+1)] for i in range(N+1)]
G=sub(sub(one,sx),ty)
test(G,"1-s-t")
test(sub(one,mul(sx,ty)),"1-st")
test(sub(one,pw(sx,2)),"1-s^2")
test(sub(one,mul(pw(sx,2),ty)),"1-s^2t")
test(sub(one,mul(pw(sx,5),pw(ty,5))),"1-s^5t^5")
test(sub(one,sx),"1-s")
