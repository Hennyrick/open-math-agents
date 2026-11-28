import itertools, sympy as sp
x,y=sp.symbols('x y'); r=sp.sqrt(-3); w=(-1+r)/2
K=(1+x+x**2)*(1+y+y**2)-x*y
mu=[1,-1,w,w**2,-w,-w**2]
lin=[]
for z in mu:
  lin.append(('1-%sx'%z,1-z*x)); lin.append(('1-%sy'%z,1-z*y))
found=0
for k in range(0,5):
  for combo in itertools.combinations_with_replacement(range(len(lin)),k):
    for a,b in [(0,0),(1,0),(0,1),(1,1)]:
      A=x**a*y**b*sp.prod([lin[i][1] for i in combo])
      if sp.expand(A).subs({x:0,y:0})!=1: continue
      for (c1,c2) in [(-w**2,-w),(-w,-w**2)]:
        B=sp.expand((K-c1*A)*(c1))
        if sp.simplify(sp.expand(B.subs({x:0,y:0}))-1)!=0: continue
        f=sp.factor_list(B,extension=r)
        ok=all(sp.Poly(fac,x,y).total_degree()<=1 or sp.simplify(fac-K)==0 for fac,m in f[1])
        if ok:
          found+=1; print("A=",sp.factor(A,extension=r)," B=",sp.factor(B,extension=r), (c1,c2))
print("found",found)
