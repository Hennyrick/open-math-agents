import random
from fractions import Fraction as Fr
exec(open('hint.py').read().split('random.seed')[0])
def plog(c,p,M=60):
  # (1/p) log(c^(p-1)) as exact rational truncation
  w=Fr(c)**(p-1)-1; s=Fr(0); t=Fr(1)
  for k in range(1,M):
    t*=w; s+=(-1)**(k+1)*t/k
  return s/p
random.seed(3)
for kap in [2,3,Fr(1,2),6]:
  u=[Fr(1)]+[Fr(random.randint(-3,3)) for _ in range(5)]+[Fr(0)]*(N-5)
  f=[Fr(0)]+[kap*x for x in u[:N]]
  for p in [5,7]:
    Uu=[x-y/p for x,y in zip(log1(u),phi(log1(u),p))]
    Uf=[Uu[0]+plog(kap,p)]+Uu[1:]
    omf=[Fr(1)]+[-x for x in f[1:]]
    H=[x-y/(p*p)+w for x,y,w in zip(li2(f),phi(li2(f),p),mul(Uf,log1(omf)))]
    # integrality up to p-adic precision of the truncated log (~ p^50): check v>=0 for coefficients
    bad=[n for n in range(1,80) if v(H[n],p)<0 and v(H[n],p)>-40]
    print("kappa",kap,"p",p,"nonintegral:",bad[:6])
