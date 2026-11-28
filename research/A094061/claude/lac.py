import itertools, sys, json, ast
import sympy as sp
from sympy.combinatorics import Permutation
def e23(n):
  n=abs(n);a=b=0
  while n%2==0:n//=2;a+=1
  while n%3==0:n//=3;b+=1
  assert n==1; return a,b
pairs=[]
# normalized pairs from la-format files
for fn in sys.argv[2:]:
  for line in open(fn):
    line=line.strip()
    if line.startswith('(('):
      (a,b),s,num,fac=ast.literal_eval(line)
      h=dict(num); h['x']=h.get('x',0)+a; h['y']=h.get('y',0)+b
      omh=dict(fac)
      for n,e in num.items():
        if e<0: omh[n]=omh.get(n,0)+e
      pairs.append((h,omh,'tang'))
    elif line.startswith('{'):
      d=json.loads(line); a,b=d['mono']; kn,kd=d['kappa']
      h=dict(d['num']); h['x']=h.get('x',0)+a; h['y']=h.get('y',0)+b
      e2n,e3n=e23(kn); e2d,e3d=e23(kd)
      h['c2']=h.get('c2',0)+e2n-e2d; h['c3']=h.get('c3',0)+e3n-e3d
      omh=dict(d['omh']); c2,c3=e23(d['omh_c'])
      omh['c2']=omh.get('c2',0)+c2-e2d; omh['c3']=omh.get('c3',0)+c3-e3d
      for n,e in d['num'].items():
        if e<0: omh[n]=omh.get(n,0)+e
      h0 = 0 if (a,b)!=(0,0) else d['sign']*kn/kd
      typ='tang' if h0 in (0,1) else 'unit%s'%h0
      pairs.append((h,omh,typ))
allowed=sys.argv[1].split(',')
pairs=[p for p in pairs if any(p[2].startswith(t) for t in allowed)]
names=sorted({n for h,o,_ in pairs for n in list(h)+list(o)}|{'x','y','K','c2','c3'})
n=len(names); I={k:i for i,k in enumerate(names)}
print(len(pairs),"pairs",sorted({p[2] for p in pairs}))
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
for h,o,_ in pairs:
  for c in range(n):
    e=[0]*n; e[c]=1; rels.append(w3(v(h),v(o),e))
C=[I['c2'],I['c3']]
for c1 in C:
  for c2 in C:
    for c in range(n):
      a=[0]*n;b=[0]*n;e=[0]*n;a[c1]=1;b[c2]=1;e[c]=1
      if c1!=c2: rels.append(w3(a,b,e))
M=sp.Matrix(rels).T; rk=M.rank()
X=v({'x':1});Y=v({'y':1});Kv=v({'K':1})
print("rank",rk,"x^y^K in span:",M.row_join(sp.Matrix(w3(X,Y,Kv))).rank()==rk)
