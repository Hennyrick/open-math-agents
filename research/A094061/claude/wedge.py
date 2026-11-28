import itertools, sympy as sp
from sympy.combinatorics import Permutation
# basis of multiplicative group (mod torsion): 
B=['x','y','P1x','P2x','P3x','P1y','P2y','P3y','G']
idx={b:i for i,b in enumerate(B)}
n=len(B)
def vec(**kw):
  v=[0]*n
  for k,c in kw.items(): v[idx[k]]+=c
  return v
X=vec(x=1); Y=vec(y=1)
onepx=vec(P2x=1,P1x=-1); onepy=vec(P2y=1,P1y=-1)
Tx=vec(P3x=1,P1x=-1); Ty=vec(P3y=1,P1y=-1)
def add(*vs):
  r=[0]*n
  for c,v in vs:
    for i in range(n): r[i]+=c*v[i]
  return r
sig=add((1,X),(-2,onepx)); tau=add((1,Y),(-2,onepy))
omsig=add((1,Tx),(-2,onepx)); omtau=add((1,Ty),(-2,onepy))
Gv=vec(G=1)
K=add((2,onepx),(2,onepy),(1,Gv))
pairs=[]
# 1D pairs in x and y
for (var,Pa) in [('x',lambda a:'P%dx'%a),('y',lambda a:'P%dy'%a)]:
  Z=X if var=='x' else Y
  for a in [1,2,3]:
    if a<=3: pairs.append((add((a,Z)), vec(**{Pa(a):1})))
  for a in [1]:
    pairs.append((add((1,Z)), add((1,vec(**{Pa(2):1})),(-1,vec(**{Pa(1):1})))))  # -z, 1+z
  # five-term z(1-z^2)/(1-z^3), (1-z)/(1-z^3)
  pairs.append((add((1,Z),(1,vec(**{Pa(2):1})),(-1,vec(**{Pa(3):1}))), add((1,vec(**{Pa(1):1})),(-1,vec(**{Pa(3):1})))))
  pairs.append((add((2,Z),(1,vec(**{Pa(1):1})),(-1,vec(**{Pa(3):1}))), add((1,vec(**{Pa(2):1})),(-1,vec(**{Pa(3):1})))))
pairs.append((sig,omsig)); pairs.append((tau,omtau))
# 2D
pairs.append((add((1,sig),(-1,omtau)), add((1,Gv),(-1,omtau))))   # sigma/(1-tau), G/(1-tau)
pairs.append((add((1,tau),(-1,omsig)), add((1,Gv),(-1,omsig))))
pairs.append((add((1,sig),(1,tau),(-1,omsig),(-1,omtau)), add((1,Gv),(-1,omsig),(-1,omtau))))
pairs.append((add((1,sig),(-1,Gv)), add((1,omtau),(-1,Gv))))  # -sigma/G, (1-tau)/G
pairs.append((add((1,tau),(-1,Gv)), add((1,omsig),(-1,Gv))))
pairs.append((add((1,sig),(1,tau),(-1,Gv)), add((1,omsig),(1,omtau),(-1,Gv))))
# wedge^3 coordinates
trip=list(itertools.combinations(range(n),3)); tid={t:i for i,t in enumerate(trip)}
def w3(a,b,c):
  r=[0]*len(trip)
  for i in range(n):
    for j in range(n):
      for k in range(n):
        co=a[i]*b[j]*c[k]
        if co==0 or len({i,j,k})<3: continue
        perm=[i,j,k]; s=sorted(perm)
        sign=Permutation([s.index(q) for q in perm]).signature()
        r[tid[tuple(s)]]+=sign*co
  return r
rels=[]
for (h,omh) in pairs:
  for c in range(n):
    e=[0]*n; e[c]=1
    rels.append(w3(h,omh,e))
M=sp.Matrix(rels).T
target=sp.Matrix(w3(X,Y,Gv))
print("rank",M.rank(), "aug",M.row_join(target).rank())
def inspan(t):
  return M.rank()==M.row_join(sp.Matrix(t)).rank()
A=w3(X,Y,Gv); Dd=w3(onepx,onepy,Gv)
print("A-4Dd in span:", inspan([a-4*d for a,d in zip(A,Dd)]))
print("Dd in span:", inspan(Dd))
