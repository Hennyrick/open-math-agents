# Independent audit of the A023871 Euclidean chains

The Cartier estimate in the public [Euler-product moment reduction](https://github.com/rbajaj5/a183068-supercongruence/blob/e6955c6a329a713e7ed7b3f1dca165f587131c90/related-results/EulerProductCubicCartierMoments.md) asks whether, for every prime \(p\ge7\), \(s\ge1\) and positive \(N\) divisible by \(p^s\), the degree-\(N\) coefficient of
\[
\left(\sum_{a,x>0,\ p\nmid x} \frac{a^2}{x}z^{ax}\right)^2
\]
is divisible by \(p^s\) in the localisation of the integers at \(p\).

## Chains

Put \(q=p^s\). Consider all quadruples of positive integers satisfying \(ax+by=N\) and \(p\nmid\gcd(x,y)\). There is a unique residue \(t\) modulo \(q\) satisfying \(ty=a\) and \(tx=-b\), since at least one of \(x,y\) is a unit and \(ax+by=0\bmod q\). Give each state weight \(t^4xy\). Denote their sum by \(P_s(N)\). Its restriction \(W_s(N)\) to states with \(x,y\) both units equals the required coefficient modulo \(q\), because \(t^4xy=a^2b^2/(xy)\) on these states.

If \(a>b\), move from \((a,b,x,y)\) to \((a-b,b,x,x+y)\). If \(a<b\), interchange the coordinate pairs in this rule. The moves preserve the equation, \(\gcd(x,y)\), and \(t\). Their direction is determined forwards by comparing \(a,b\) and backwards by comparing \(x,y\). The moves terminate because \(a+b\) strictly decreases forwards and \(x+y\) strictly decreases backwards. Thus each state lies on one chain starting at \(x=y=g\) and ending at \(a=b=h\). The terminal \(x,y\) satisfy \(x+y=d=N/h\), and \(g=\gcd(x,d)\).

Let \(Q(x,y)=(x^2-xy+y^2)/2\). In each move the change in \(Q\) is \(xy\). Including the terminal contribution, the sum of \(xy\) along the entire chain is \((d^2-x(d-x)-g^2)/2\). Each positive divisor pair \(hd=N\) and each \(1\le x<d\) with \(p\nmid\gcd(x,d)\) specify one terminal chain.

If \(p\nmid d\), then \(q\mid h\) and \(t=0\). If \(p\mid d\), then \(p\nmid xy\) and \(t=-h/x\). Put \(v=v_p(h)\) and \(w=v_p(d)\). Since \(4v+w\ge s\), multiplication by \(h^4 d\) gives zero modulo \(q\). The chain contribution therefore equals \(h^4(x^2-g^2)/(2x^4)\bmod q\). In the sum with \(g\) fixed, write \(x=gk\) and \(e=d/g\). The variable \(k\) runs through every unit class modulo \(e\) once. The contribution of this group is
\[
\frac{h^4}{2g^2}\sum_{k\in(\mathbb Z/e)^\times}(k^{-2}-k^{-4})\pmod q.
\]
Here inverse powers use the positive integer representatives modulo \(q\). Only their reductions modulo \(p^{\min(w,s)}\) are needed. Reduction from the units modulo \(e\) to units modulo \(p^w\) is surjective with constant fibre size by the Chinese remainder theorem, since \(p\nmid g\). Each of the two inverse-power sums vanishes modulo \(p^w\). Multiplication by a unit whose reduction generates \(\mathbb F_p^\times\) permutes the residues modulo \(p^w\). Neither its square nor its fourth power equals \(1\bmod p\), because \(p-1>4\). Multiplication by \(h^4\) finishes the congruence. Thus \(P_s(N)=0\bmod p^s\).

For the restriction \(W_s(N)\), a state with \(p\mid x\) has \(y\) a unit and \(p\mid b\). Divide \(x,b\) by \(p\). This gives a bijection onto the states at \(N/p\) with \(y\) a unit. The original weight reduces to \(p\) times the new weight modulo \(p^s\), since \(t=a/y\) before and after division, reduced modulo \(p^{s-1}\) at the lower level. Interchanging the coordinate pairs accounts for the case \(p\mid y\), with no sign change in \(t^4\). Together these contributions count the lower-level states once if just one coordinate is a unit and twice if both are units. For \(s>1\),
\[
W_s(N)=P_s(N)-p(P_{s-1}(N/p)+W_{s-1}(N/p))\pmod {p^s}.
\]
At \(s=1\) every removed summand already contains \(p\). Induction gives \(W_s(N)=0\bmod p^s\).

## Reproduction

From this directory, with Python 3.10 or later, run

    python check_chains.py
    python check_cartier.py 1013 1 32
    python check_cartier.py 149 2 9
    python check_cartier.py 31 3 8

The first script checks both map directions, unique covering by chains, the slope relation at every state, telescoping including both ends, each terminal contribution, grouped unit sums, the nonunit-coordinate recursion, and an independent exact-rational convolution. Its 82 full instances comprise 342,258 states. The other three commands use a divisor sieve and modular convolution to check 5,331, 287, and 63 coefficients at the indicated valuation depths. These finite checks audit the formulas. The uniform argument is above.

The public Euler-product moment reduction then gives the full all-level congruence. The programs here test the Cartier estimate. They do not run the Lean checker.
