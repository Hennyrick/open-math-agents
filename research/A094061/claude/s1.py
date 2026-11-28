from fractions import Fraction as F
N=400
# sqrt series of 1 + (2/3)x + x^2, inverse
c=[F(1),F(2,3),F(1)]+[F(0)]*(N)
# h = c^{-1/2}: h' / h = -1/2 c'/c  => c h' = -1/2 c' h
h=[F(0)]*(N+1); h[0]=F(1)
for n in range(N):
  # coefficient n of c*h' + 1/2 c'*h = 0 ; (c h')_n = sum c_i (n-i+1) h_{n-i+1}
  # solve for h_{n+1}: c0 (n+1) h_{n+1} + sum_{i>=1} c_i (n-i+1)h_{n-i+1} + 1/2 sum_i (i+1)c_{i+1} h_{n-i} = 0
  s=F(0)
  for i in range(1,3):
    if n-i+1>=0: s+=c[i]*(n-i+1)*h[n-i+1]
  for i in range(0,2):
    if n-i>=0: s+=F(1,2)*(i+1)*c[i+1]*h[n-i]
  h[n+1]=-s/(n+1)
# pre = x(1-x)/(1+x+x^2) = x(1-x)^2/(1-x^3)
pre=[F(0)]*(N+1)
num=[0,1,-2,1]
for k in range(0,N+1,3):
  for i,a in enumerate(num):
    if k+i<=N: pre[k+i]+=a
g=[sum(pre[i]*h[n-i] for i in range(n+1)) for n in range(N+1)]
def v(fr,p):
  if fr==0: return 99
  a,b=fr.numerator,fr.denominator; e=0
  while a%p==0: a//=p; e+=1
  while b%p==0: b//=p; e-=1
  return e
for p in [5,7,11,13,17,19,23]:
  chi = 1 if p%3==1 else -1
  worst=99; fails=[]
  for n in range(1,N//p+1):
    d=g[p*n]-chi*g[n]
    vv=v(d,p); need=2*(1+v(F(n),p))
    if vv<need: fails.append((n,vv,need))
    worst=min(worst,vv-need)
  print(p,"fails",fails[:5],"min slack",worst)
