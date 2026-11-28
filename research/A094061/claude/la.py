import itertools, sys, ast
import sympy as sp
from sympy.combinatorics import Permutation
pairs=[]
for fn in sys.argv[1:]:
  for line in open(fn):
    if line.startswith('(('):
      (a,b),s,num,fac=ast.literal_eval(line.strip())
      h=dict(num); 
      if a: h['x']=h.get('x',0)+a
      if b: h['y']=h.get('y',0)+b
      # 1-h = fac / den ; den = prod of negative exps of num
      omh=dict(fac)
      for n,e in num.items():
        if e<0: omh[n]=omh.get(n,0)+e
      pairs.append((h,omh))
names=sorted({n for h,o in pairs for n in list(h)+list(o)}|{'x','y','K'})
n=len(names); I={k:i for i,k in enumerate(names)}
print(len(pairs),"pairs; basis",names)
def v(d):
  r=[0]*n
  for k,e in d.items(): r[I[k]]+=e
  return r
trip=list(itertools.combinations(range(n),3)); tid={t:i for i,t in enumerate(trip)}
def w3(a,b,c):
  r=[0]*len(trip)
  for i in range(n):
    if not a[i]: continue
    for j in range(n):
      if not b[j] or j==i: continue
      for k in range(n):
        if not c[k] or k in (i,j): continue
        perm=[i,j,k]; s=sorted(perm)
        r[tid[tuple(s)]]+=Permutation([s.index(q) for q in perm]).signature()*a[i]*b[j]*c[k]
  return r
rels=[]
for h,o in pairs:
  for c in range(n):
    e=[0]*n; e[c]=1; rels.append(w3(v(h),v(o),e))
M=sp.Matrix(rels).T
rk=M.rank()
def ins(t): return M.row_join(sp.Matrix(t)).rank()==rk
X=v({'x':1});Y=v({'y':1});Kv=v({'K':1});px=v({'P2x':1,'P1x':-1});py=v({'P2y':1,'P1y':-1})
print("rank",rk,"x^y^K in span:",ins(w3(X,Y,Kv)),"  (1+x)^(1+y)^K:",ins(w3(px,py,Kv)))
