import itertools, mpmath as mp, sympy as sp
mp.mp.dps=40
s3=mp.sqrt(3); I=mp.mpc(0,1)
a0=1+s3
pts={'a0':a0,'a1':1-s3,'p1':-1+s3,'p2':-1-s3,'b1':I*(1+s3),'b2':I*(1-s3),'q1':I*(-1+s3),'q2':I*(-1-s3),'z':mp.mpc(0)}  # plus infinity 'oo'
names=list(pts)+['oo']
n=len(names); ix={k:i for i,k in enumerate(names)}
def X(t): return -(t*t-2*t-2)/(t*t+2*t-2)
dX=mp.diff(X,a0)
def isroot(z):
  z=mp.mpc(z)
  if abs(abs(z)-1)>1e-25: return False
  for m in range(1,25):
    if abs(z**m-1)<1e-25: return True
  return False
def div(d):
  v=[0]*n
  for k,e in d.items(): v[ix[k]]+=e
  return v
# div of X: zeros a0,a1; poles p1,p2.  Y: zeros b1,b2; poles q1,q2
DX=div({'a0':1,'a1':1,'p1':-1,'p2':-1}); DY=div({'b1':1,'b2':1,'q1':-1,'q2':-1})
def val(k,t):  # t - point, or 1 for oo
  return 1 if k=='oo' else t-pts[k]
rels=[]
finite=[k for k in names]
# f = (t-al)(ga-be)/((t-be)(ga-al)) ; f(ga)=1, f(al)=0, f(be)=oo ; 1-f = (t-ga)(al-be)/((t-be)(al-ga))
def fval(al,be,ga,t):
  def L(k): return 1 if k=='oo' else (t-pts[k])
  def C(k1,k2):
    if k1=='oo' and k2=='oo': return 1
    if k1=='oo': return 1
    if k2=='oo': return -1
    return pts[k1]-pts[k2]
  return None
cnt=0
for al,be,ga in itertools.permutations(names,3):
  # cross ratio value at a0 via formula with oo handled by limits; compute numerically using large R for oo
  R=mp.mpf(10)**30
  P={k:(pts[k] if k!='oo' else R) for k in names}
  def f(t): return (t-P[al])*(P[ga]-P[be])/((t-P[be])*(P[ga]-P[al]))
  if 'a0' not in (al,be,ga):
    v=f(a0)
    if isroot(v) and isroot(1-v):
      Df=div({al:1,be:-1}); D1f=div({ga:1,be:-1})
      rels.append((Df,D1f,'unit',(al,be,ga))); cnt+=1
  else:
    # tangential: leading coefficient in X at a0 must be root of unity (for the vanishing one) and value root of unity (other)
    g=lambda t: 1-f(t)
    for F,G_,lab in [(f,g,'f'),(g,f,'1-f')]:
      if (al=='a0' and lab=='f') or (ga=='a0' and lab=='1-f'):
        lc=mp.diff(F,a0)/dX
        if isroot(lc) and isroot(G_(a0)):
          rels.append((div({al:1,be:-1}),div({ga:1,be:-1}),'formal',(al,be,ga))); cnt+=1
print("pairs",cnt)
for r in rels: print(r[2],r[3])
trip=list(itertools.combinations(range(n),2)); tid={t:i for i,t in enumerate(trip)}
def w2(a,b):
  r=[0]*len(trip)
  for i in range(n):
    for j in range(n):
      if i<j: r[tid[(i,j)]]+=a[i]*b[j]-a[j]*b[i]
  return r
M=sp.Matrix([w2(a,b) for a,b,_,_ in rels]).T
rk=M.rank(); tgt=sp.Matrix(w2(DX,DY))
print("rank",rk,"target in span:",M.row_join(tgt).rank()==rk)
D1X=div({'z':1,'oo':1,'p1':-1,'p2':-1}); D1Y=div({'z':1,'oo':1,'q1':-1,'q2':-1})
def ins(a,b): return M.row_join(sp.Matrix(w2(a,b))).rank()==rk
print("X^1+Y",ins(DX,D1Y),"1+X^Y",ins(D1X,DY),"1+X^1+Y",ins(D1X,D1Y))
# tame symbol rank: compute dimension of kernel heuristically via random numeric relations? skip
