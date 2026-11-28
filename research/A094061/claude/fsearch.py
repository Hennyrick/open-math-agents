import itertools, flint, sys
R=flint.fmpz_mpoly_ctx.get(('x','y'),'lex'); x,y=R.gens()
G={'P1x':1-x,'P2x':1+x,'P3x':1+x+x**2,'P4x':1+x**2,'P6x':1-x+x**2,
   'P1y':1-y,'P2y':1+y,'P3y':1+y+y**2,'P4y':1+y**2,'P6y':1-y+y**2,
   'K':(1+x+x**2)*(1+y+y**2)-x*y}
known={}
for n,g in list(G.items())+[('x',x),('y',y)]:
  c,f=g.factor(); assert len(f)==1; known[str(f[0][0])]=n
use=sys.argv[1].split(','); rngs=[eval(r) for r in sys.argv[2].split(';')]
pw={n:{} for n in use}
out=[]
newfac={}
for a,b in [(1,0),(0,1),(1,1),(2,0),(0,2),(2,1),(1,2),(2,2)]:
  mono=x**a*y**b
  for es in itertools.product(*rngs):
    num=mono; den=R.from_dict({(0,0):1})
    for n,e in zip(use,es):
      if e>0: num=num*G[n]**e
      elif e<0: den=den*G[n]**(-e)
    for s in (1,-1):
      P=den-s*num
      c,f=P.factor()
      if abs(c)!=1: continue
      names=[known.get(str(q)) for q,m in f]
      if all(names):
        out.append(((a,b),s,{n:e for n,e in zip(use,es) if e},{nm:m for nm,(q,m) in zip(names,f)}))
      elif sum(1 for nm in names if nm is None)==1:
        q=[str(q) for (q,m),nm in zip(f,names) if nm is None][0]
        newfac[q]=newfac.get(q,0)+1
for o in out: print(o)
print("count",len(out))
print("single-new-factor candidates:",sorted(newfac.items(),key=lambda t:-t[1])[:15])
