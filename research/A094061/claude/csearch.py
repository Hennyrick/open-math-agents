import itertools, flint, sys, json
from fractions import Fraction as Fr
R=flint.fmpz_mpoly_ctx.get(('x','y'),'lex'); x,y=R.gens()
G={'P1x':1-x,'P2x':1+x,'P3x':1+x+x**2,'P4x':1+x**2,'P6x':1-x+x**2,
   'P1y':1-y,'P2y':1+y,'P3y':1+y+y**2,'P4y':1+y**2,'P6y':1-y+y**2,
   'K':(1+x+x**2)*(1+y+y**2)-x*y,'Qp':1+x*y,'Qm':1-x*y}
known={}
for n,g in list(G.items())+[('x',x),('y',y)]:
  c,f=g.factor(); known[str(f[0][0])]=n
def smooth23(c):
  c=abs(c); e2=e3=0
  while c%2==0: c//=2; e2+=1
  while c%3==0: c//=3; e3+=1
  return (e2,e3) if c==1 else None
spec=json.loads(sys.argv[1]); use=list(spec); rngs=[range(spec[k][0],spec[k][1]+1) for k in use]
kappas=[Fr(1),Fr(2),Fr(4),Fr(1,2),Fr(1,4),Fr(3),Fr(1,3),Fr(2,3),Fr(3,2),Fr(3,4),Fr(4,3)]
for a,b in [(1,0),(0,1),(1,1),(2,0),(0,2),(0,0)]:
  mono=x**a*y**b
  for es in itertools.product(*rngs):
    num=mono; den=R.from_dict({(0,0):1})
    for n,e in zip(use,es):
      if e>0: num=num*G[n]**e
      elif e<0: den=den*G[n]**(-e)
    for k in kappas:
      for s in (1,-1):
        if (a,b)==(0,0) and k==1: continue
        # 1-h = (den*kd - s*kn*num)/(den*kd)
        P=den*k.denominator - s*k.numerator*num
        if P==0: continue
        c,f=P.factor()
        if c==0 or smooth23(int(c)) is None: continue
        names=[known.get(str(q)) for q,m in f]
        if all(names):
          print(json.dumps({"mono":[a,b],"sign":s,"kappa":[k.numerator,k.denominator],"num":{n:e for n,e in zip(use,es) if e},"omh_c":int(c),"omh":{nm:m for nm,(q,m) in zip(names,f)}}),flush=True)
