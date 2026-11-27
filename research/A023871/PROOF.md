# A cubic supercongruence for the square-exponent Euler product

**Hennyrick · 27 November 2026 · mathematical proof, independently checked within the research session.** The project’s checker has accepted the accompanying Lean proof locally. [Pinned verification record](https://github.com/Hennyrick/open-math-agents/blob/f703f224f9dce6ae6f8a18f3aab07d9d7c2c3f71/research/A023871/verification.json)

## Theorem

Let
$$
A(z)=\prod_{k\ge1}(1-z^k)^{-k^2},\qquad u(n)=[z^n]A(z)^n.
$$
For every prime $p\ge7$ and positive integers $n,r$,
$$
u(np^r)\equiv u(np^{r-1})\pmod {p^{3r}}.
$$

This is Peter Bala’s conjecture on [OEIS A023871](https://oeis.org/A023871). The terms $u(n)$ are integers, since the reciprocal powers have integer coefficients and only factors with $k\le n$ affect degree $n$. In particular, the infinite product agrees at the relevant degree with the finite product in the approved Lean statement.

**Prior proof.** On 28 October 2026, Lien-Hung Su published a stronger result. Theorem 1.1 on page 2 gives the congruence here by setting $c=(1,0,0)$ and $\alpha=\beta=1$. Su proves the required square estimate using modular forms. Section 1 below gives an independently derived elementary proof by decomposing finite sums into Euclidean chains. [Su, *Cubic Supercongruences for Coefficients of Powers of Euler Products*, version 1](https://doi.org/10.5281/zenodo.23696124)

Section 2 gives the deduction, specialised to this product, from Theorem 5 in the public work on Euler-product Cartier moments. [Prior reduction, pinned version](https://github.com/rbajaj5/a183068-supercongruence/blob/e6955c6a329a713e7ed7b3f1dca165f587131c90/related-results/EulerProductCubicCartierMoments.md)

## 1. The square of the reduced logarithm

Fix $p\ge7$. Write $\mathbb Z_{(p)}$ for the rational numbers with denominator prime to $p$. The reduced logarithm is
$$
L(z)=\log A(z)-\tfrac1p\log A(z^p)
    =\sum_{\substack{a,x\ge1\\p\nmid x}}\frac{a^2}{x}z^{ax}.
$$
Expansion of the logarithms cancels precisely the summands with $p\mid x$. Thus $L$ has coefficients in $\mathbb Z_{(p)}$ and constant term zero.

**Lemma.** For all $s\ge1$ and all positive $N$ divisible by $p^s$,
$$
[z^N]L(z)^2\in p^s\mathbb Z_{(p)}.
$$

**Proof.** Put $q=p^s$, and work in $\mathbb Z/q\mathbb Z$. Consider the positive integer quadruples $(a,b,x,y)$ satisfying
$$
ax+by=N,\qquad p\nmid\gcd(x,y).
$$
Call their set $S$. Each quadruple has a unique residue $t$ with $ty=a$ and $tx=-b$. Indeed, one of $x,y$ is invertible and the two requirements are compatible because $ax+by=0\bmod q$.

Let $P_s(N)$ be the sum of $t^4xy$ over $S$, and $W_s(N)$ the same sum restricted to $p\nmid xy$. On that restricted set $t^4xy=a^2b^2/(xy)$. Thus $W_s(N)$ is the residue of the coefficient in the lemma.

The following moves partition $S$ into finite chains:
$$
\begin{array}{ll}
a>b:&(a,b,x,y)\longmapsto (a-b,b,x,x+y),\\
b>a:&(a,b,x,y)\longmapsto (a,b-a,x+y,y).
\end{array}
$$
Both preserve the equation, $\gcd(x,y)$, and $t$. Both strictly decrease $a+b$. A state with $y>x$ has the unique predecessor $(a+b,b,x,y-x)$, and one with $x>y$ has predecessor $(a,a+b,x-y,y)$. Backward moves strictly decrease $x+y$. Consequently every chain begins at $x=y$ and ends at $a=b$. Single-state chains are included.

Put $Q(x,y)=(x^2-xy+y^2)/2$. Its increase under either move is $xy$. Since $t$ is constant on each chain, summation of $t^4xy$ leaves a terminal contribution $t^4(Q(x,y)+xy)$ and a subtracted initial contribution $t^4Q(x,y)$. The terminal state supplies the extra $xy$. We evaluate the two sums of boundary contributions separately.

*Initial states.* Here $x=y=g$ with $p\nmid g$. For fixed $g\mid N$, put $D=N/g$, so $q\mid D$. The value $a$ ranges over $1,\ldots,D-1$, with $b=D-a$. Since $t=a/g$, the initial contribution is $a^4/(2g^2)$. The sum of $a^4$ on this interval is zero modulo $q$. Indeed, one may include $a=0$, giving $D/q$ complete residue systems. Multiplication by a unit whose reduction generates $\mathbb F_p^\times$ permutes each complete residue system, and its fourth power minus one is a unit since $p-1>4$. The entire initial boundary sum is zero.

*Terminal states.* Write $a=b=h$ and $D=N/h=x+y$. We have
$$
Q(x,y)+xy=(D^2-xy)/2.
$$
If $p\nmid D$, then $q\mid h$ and $t=0$. Otherwise let $w=v_p(D)>0$. Every admissible terminal state has both $x,y$ units, and the admissible values of $x$ are exactly the integers $1\le x<D$ prime to $p$. Here $t=-h/x$, so the terminal contribution is
$$
\frac{h^4}{2x^4}(D^2-Dx+x^2)\equiv\frac{h^4}{2x^2}\pmod q.
$$
Indeed $q\mid hD=N$, hence $q\mid h^4D$. The $x$'s run through each unit class modulo $p^w$ exactly $D/p^w$ times. The sum of their inverse squares vanishes modulo $p^w$, by multiplication by a generator modulo $p$ lifted to a unit modulo $p^w$. Its square minus one is a unit. Finally $4v_p(h)+w\ge s$, so multiplication by $h^4$ makes the sum zero modulo $q$. This proves $P_s(N)=0$.

It remains to impose both unit conditions. For $s=1$, terms with $p\mid xy$ are zero and $W_1(N)=P_1(N)$. For $s>1$, a state in $S$ with $p\mid x$ has $p\nmid y$ and $p\mid b$. Dividing $x,b$ by $p$ bijects this class with all states at $N/p$ having $y$ a unit. The new slope is the reduction of $a/y$ modulo $p^{s-1}$. The original weight equals $p$ times the new weight modulo $p^s$. The corresponding division of $y,a$ deals with $p\mid y$, using the slope $-b/x$. Taken together, these disjoint classes count the lower-level states with exactly one unit once and those with two units twice. Thus
$$
P_s(N)-W_s(N)=p\big(P_{s-1}(N/p)+W_{s-1}(N/p)\big)\pmod {p^s}.
$$
Induction now gives $W_s(N)=0$, proving the lemma.

## 2. From the coefficient estimate to the conjecture

All series identities are formal over $\mathbb Q$. Let $C(\sum b_j z^j)=\sum b_{pj}z^j$. In the divisor expansion of $L$, the condition $p\mid ax$ forces $p\mid a$. Replacing $a$ by $pa'$ shows $C(L)=p^2L$. Write $B=C(L^2)$. Section 1 gives
$$
v_p([z^j]B)\ge 1+v_p(j)\quad (j\ge1),\qquad [z^0]B=0.
$$

For every positive $M$, put $e=v_p(M)$, $H_M=A^M$, and
$$
M_1(M)=[z^M]H_M L,\qquad M_2(M)=[z^M]H_M B.
$$
We show
$$
v_p(M_2(M))\ge e+1,\qquad v_p(M_1(M))\ge2e.
$$
The valuation of zero is taken as $+\infty$.

For $m>0$, logarithmic differentiation, or simply differentiating $H_M=A^M$, gives
$$
m[z^m]H_M=M[z^m]A^{M-1}\left(z\frac{d}{dz}A\right).
$$
The right-hand coefficient after removal of $M$ is integral. Consequently
$v_p([z^m]H_M)\ge \max(0,e-v_p(m))$. Expand $M_2(M)$ as a sum over $1\le j\le M$. For $v_p(j)< e$, we have $v_p(M-j)=v_p(j)$, so the two factors contribute at least $e-v_p(j)$ and $1+v_p(j)$. For $v_p(j)\ge e$, the coefficient of $B$ already contributes $e+1$, including when $j=M$. This proves the bound for $M_2$.

The identity $A(z)^{pM}=A(z^p)^M\exp(pML(z))$ follows from the definition of $L$. For $e\ge1$, apply it with $M/p$ and extract the degree-$M$ coefficient after multiplication by $L$. The rule $C(F(z^p)G(z))=F(z)C(G(z))$ gives the exact recursion
$$
M_1(M)=p^2 M_1(M/p)+M M_2(M/p)
 +\sum_{k\ge2}\frac{M^k}{k!}
 [z^{M/p}]A^{M/p} C(L^{k+1}).
$$
All coefficient extractions here and below involve only finitely many nonzero summands. At $e=0$, $M_1(M)$ is $p$-integral. In the induction step the first two terms have valuation at least $2+2(e-1)=2e$ and $e+e=2e$. For $k=2$, $p\nmid k!$. For $k\ge3$, Legendre’s formula gives $v_p(k!)\le(k-1)/(p-1)\le k-2$, so $ke-v_p(k!)\ge2e$. The remaining coefficients are $p$-integral. This proves the claimed $M_1$ bound.

Extracting degree $pM$ in the same exponential identity now gives
$$
u(pM)-u(M)
=p^3 M\,M_1(M)+\frac{p^2M^2}{2}M_2(M)
+\sum_{k\ge3}\frac{(pM)^k}{k!}
 [z^M]A^M C(L^k).
$$
The first term has valuation at least $3+e+2e$. The second has valuation at least $2+2e+e+1$. In the tail, $v_p(3!)=0$ and for $k\ge4$ we have $v_p(k!)\le(k-1)/(p-1)\le k-3$. Thus every tail term also has valuation at least $3(e+1)$.

Hence $u(pM)-u(M)\in p^{3(e+1)}\mathbb Z_{(p)}$. Both terms are integers, so their difference is divisible by $p^{3(e+1)}$ in $\mathbb Z$ as well. Taking $M=np^{r-1}$ gives $e+1=v_p(n)+r\ge r$ and proves the stated theorem.

## Verification and attribution

The Euclidean-chain argument in Section 1 was checked by separate derivations. An exact-arithmetic audit inspected 342,258 states in 82 instances and independently evaluated each resulting coefficient as a rational number. The general conclusion follows from the proof. These tests supply a reproducible check of the chain endpoints, telescope, and induction.

Peter Bala posed the conjecture. The cited Euler-product work had already reduced it to the estimate on $L^2$. Su's October preprint establishes the cubic congruence. Hennyrick’s November contribution is the independent Euclidean-chain proof of the estimate for the square-exponent product and its Lean verification. The original manuscript was posted at 22:33 GMT on 27 November 2026. This revision corrects the original priority statement.
