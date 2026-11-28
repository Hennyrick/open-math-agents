import sympy as sp, itertools
m=sp.symbols('m'); r=sp.sqrt(-3); w=sp.Rational(-1,2)+r/2
X=(1+r*m)/(m*(m-r))
Yn=(1+r)*m**2+2*m+(1-r); Yd=(1-r)*m**2-2*m+(1+r)
Y=Yn/Yd
x,y=sp.symbols('x y')
K=(1+x+x**2)*(1+y+y**2)-x*y
print("K(X,Y)=0:",sp.simplify(sp.together(K.subs({x:X,y:Y})))==0)
m0=sp.nsimplify(-1/r)
bz=sp.solve(Yn,m); bp=sp.solve(Yd,m)
print("Y zeros",bz,"poles",bp)
print("X(m0)=",sp.simplify(X.subs(m,m0)),"Y(m0)=",sp.simplify(Y.subs(m,m0)), "omega^2=",sp.simplify(w**2))
for b in bz+bp: print(" X(b)=",sp.nsimplify(sp.simplify(X.subs(m,b))), sp.simplify(sp.expand((X.subs(m,b))**3)))
for a in [0,r]: print(" Y(a)=",sp.simplify(Y.subs(m,a)))
print(" Y(oo)=",sp.limit(Y,m,sp.oo))
pts={'m0':m0,'p0':0,'pr':r}
for i,b in enumerate(bz): pts['b%d'%i]=b
for i,b in enumerate(bp): pts['q%d'%i]=b
for (n1,a),(n2,b) in itertools.combinations(pts.items(),2):
  d=sp.simplify(a-b); N=sp.factorrat(sp.nsimplify(sp.simplify(sp.expand(d*sp.conjugate(d)))))
  print(n1,n2,"norm factors",N)
