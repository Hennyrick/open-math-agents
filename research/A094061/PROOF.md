# A double Gauss congruence for closed king walks

**Hennyrick, 27 November 2026. Mathematical manuscript.** This argument addresses Peter Bala’s conjecture in OEIS A094061. Formal verification of the full argument is a separate task.

## Statement

Let $a(N)$ count ordered walks of length $N$ on $\mathbb Z^2$, starting and ending at the origin, with any of the eight king moves allowed. For every prime $p\ge5$ and integers $r,n\ge1$,
$$
 a(np^r)\equiv a(np^{r-1})\pmod {p^{2r}}.
$$
Bala proved the congruence modulo $p^r$ and conjectured this strengthening. The dilogarithmic Frobenius regulator and its Steinberg relation are prior work of Schwarz, Vologodsky and Walcher. We give an integral local calculation because Frobenius can exchange the two branches of the king curve. The computation of its boundary values and the two coefficient transfers connect this method to the walks.

[Bala, A note on A094061, 13 February 2022](https://oeis.org/A094061/a094061.pdf) · [OEIS A094061](https://oeis.org/A094061) · [Schwarz, Vologodsky and Walcher, Framing the Di-Logarithm (over ℤ), §§3 and 5](https://arxiv.org/abs/1306.4298) · [Approved Lean statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/de6bc039e5b90a1da812097ed59cbdd9a0209158/statements/oeis-a094061.lean)

## 1. The curve and its boundary

Put $T(z)=1+z+z^2$ and $K(x,y)=T(x)T(y)-xy$. Multiplication counts ordered steps, so $a(N)=[x^Ny^N]K^N$: each move has been shifted by $(1,1)$. Fix $p\ge5$. Take a finite unramified extension of $\mathbb Q_p$ containing $i=\sqrt{-1}$ and $d=\sqrt3$, with integer ring $O$ and arithmetic Frobenius $\sigma$. Such an extension exists since these elements lie in the field of twelfth roots of unity.

In the coordinates $u=(1-X)/(1+X)$, $v=(1-Y)/(1+Y)$, the curve $K(X,Y)=0$ becomes $u^2+v^2=-2$. With $t=u+iv$, its rational parametrisation is
$$
 X=-\frac{t^2-2t-2}{t^2+2t-2},\qquad
 Y=-\frac{t^2-2it+2}{t^2+2it+2}.
$$
Let $A$ consist of the zeros and poles of $X$, with signed multiplicities $m_a=+1,-1$ respectively, and $B$ those of $Y$, with multiplicities $n_b$. The zeros of $X$ are $1\pm d$, its poles $-1\pm d$, and the corresponding points for $Y$ are $i(1\pm d)$, $i(-1\pm d)$. All eight points have distinct reductions at $p$. Within a group the differences are, up to sign and a factor of $i$, among $2,2d,2(1\pm d)$, all units. Across groups a difference is $a-ic$ where $a,c$ are up to sign $1\pm d$. Its product with $a+ic$ is either $8$ or $2(1\pm d)^2$, a unit. Both rational functions have leading constant $-1$.

For $a\in A$, $T(Y(a))=0$. For $b\in B$, $T(X(b))=0$. At zeros set the zero coordinate to zero in $K$; at poles take the leading coefficient in that coordinate. Distinct punctures exclude simultaneous poles. The boundary values are primitive cube roots of unity.

At either zero $a_0$ of $X$, take $z=X$. Its derivative there is a unit, so formal power series inversion gives $t(z)\in a_0+zO[[z]]$ with $t'(0)$ a unit. The two series obtained for $Y$ are the distinct roots of $K(z,y)=0$ in $O[[z]]$. Indeed their constant terms are distinct: at $X=0$, the two parameters have different $v$, hence different $Y$; these cube roots remain distinct modulo $p$. The roots have product one. Denote them by $Y_1,Y_2$.

## 2. An integral primitive on each branch

Fix either branch. Put $R=O[[z]]$, $D=z\,d/dz$, and $\phi h=h^\sigma(z^p)$. For $f=z^e h$, $e\in\mathbb Z$, $h\in R^\times$, write
$$
 \lambda(f)=Df/f,\quad U(f)=p^{-1}\log(f^p/\phi f),\quad L(f)=\lambda(\phi f)/p.
$$
All three belong to $R$. In the logarithm the monomial cancels and the remaining quotient equals 1 modulo $p$. Coefficientwise $p$-adic limits with uniform precision exist in $R$. We have $DU(f)=\lambda(f)-L(f)$. Define
$$
 E(f,g)=U(f)\lambda(g)-U(g)L(f).
$$
It is additive in each multiplicative argument and $E(f,g)+E(g,f)=D(U(f)U(g))$. We work modulo the additive subgroup $DR=\{DH:H\in R\}$. For any constant root of unity $\xi$ of order prime to $p$, $U(\xi)=0$ since $\sigma(\xi)=\xi^p$. Pairing with $\xi$ therefore gives zero on either side. Pairing two constant units also gives zero.

**Steinberg calculation.** If $g=1-f$ is a unit in $R$, and $f$ is a unit or $z$ times a unit, then $E(f,g)\in DR$.

First take the lift of the pair $F_0=f^p,\ G_0=1-f^p$. Its expression is $-U_{g,0}\lambda(f)$, where $U_{g,0}=p^{-1}\log((1-f)^p/(1-f^p))$. It equals $D\mathcal D(f)$ with integral primitive given by the depleted dilogarithm. At precision $p^h$, take the rational representative
$$
 \mathcal D_h(w)=\frac{\sum_{1\le j\le p^h,\ p\nmid j} w^j/j^2}{1-w^{p^h}} .
$$
These are compatible by periodicity of the coefficients. They define an element of the $p$-adic completion of $O[w,(1-w)^{-1}]$, where each denominator is invertible since modulo $p$ it equals $(1-w)^{p^h}$. Taylor expansion at zero gives $w\mathcal D'(w)=\sum_{p\nmid j}w^j/j=-p^{-1}\log((1-w)^p/(1-w^p))$. The Taylor identity holds in the completed localisation: modulo each $p^h$, its elements have denominators powers of $1-w$, so clearing denominators proves injectivity of Taylor expansion. Substitution $w=f$ is allowed since $1-f$ is a unit. The rational representatives justify the chain rule even when $f(0)\ne0$.

For the actual lift put $\Delta=\phi f-f^p,\ F_s=f^p+s\Delta,\ G_s=1-F_s$. Both $\Delta/f^p$ and $\Delta/(1-f^p)$ belong to $pR$, including when $f$ has a simple zero. Set $U_{f,s}=p^{-1}\log(f^p/F_s)$, $U_{g,s}=p^{-1}\log(g^p/G_s)$, and $E_s=U_{f,s}\lambda(g)-U_{g,s}\lambda(F_s)/p$. Differentiation in $s$ gives
$$
 \partial_s E_s=-D\!\left(\frac{\Delta}{pF_s}U_{g,s}\right).
$$
The other two terms cancel since $(\partial_s\log G_s)D\log F_s=(\partial_s\log F_s)D\log G_s$ when $F_s+G_s=1$.

The integral on the right from $s=0$ to 1 has coefficients in $R$. Write $\theta=\Delta/f^p,\ \psi=\Delta/(1-f^p)$. The part with constant $U_{g,0}$ integrates to $U_{g,0}\log(1+\theta)/p$. The remaining terms after integration have, up to sign, the form $\theta^{k+1}\psi^j/(p^2 j(k+j+1))$, $k\ge0,\ j\ge1$. For $M=k+j+1$ their valuations are at least $M-2-v_p(j)-v_p(M)$. This is nonnegative for $M=2$ directly. For $M\ge3$, use $v_p(h)\le(h-1)/(p-1)$ and $j\le M-1,\ p\ge5$. The lower bounds tend to infinity, justifying integration and evaluation. This proves the Steinberg calculation.

For each $a\in A,b\in B$ use $f=(t-a)/(b-a)$, $g=(t-b)/(a-b)$. They satisfy the hypotheses on either branch since $b$ has different reduction from $a_0$. Expanding $E(f,g)=0$ modulo $DR$ gives
$$
 E(t-a,t-b)=E(t-a,a-b)+E(b-a,t-b)\pmod{DR}.
$$
Sum with weights $m_an_b$. For each $a$ the terms recombine to $m_aE(t-a,Y(a))$; for each $b$ they recombine to $n_bE(X(b),t-b)$. The constant factors $-1$ contribute zero. All pairings vanish by the boundary values of §1. Hence $E(X,Y)\in DR$. Since $X=z$, we have $U(X)=0$, $L(X)=1$, and therefore
$$
 U(Y)\in DR,\qquad U(Y)(0)=0 .
$$

## 3. From the branches to two-variable logarithmic coefficients

Let $q=p^s,\ s\ge1$, and $j\ge1$. For either branch put $B=(\phi Y)^{(q/p)j}$. Then $DB\in qj R$, since $D\phi Y$ is divisible by $p$ and $\phi Y$ is a unit. By §2 choose $H\in R$ with $U(Y)=DH$. We have
$$
 Y^{qj}=B\exp(qjU(Y))\equiv B+qj B\,DH\pmod {q^2jR}.
$$
Indeed the terms of degree $h\ge2$ in the exponential are divisible by $(qj)^2$, by $v_p(h!)\le h-2$ for $p\ge5,\ h\ge2$. This elementary inequality follows from Legendre’s formula, treating $h=2$ separately. For any $i\ge1$, the coefficient of $B\,DH$ at $qi$ is divisible by $q$: write it as $D(BH)-H\,DB$. Therefore
$$
 [z^{qi}]Y^{qj}\equiv
 \sigma\!\left([z^{qi/p}]Y^{qj/p}\right)\pmod {q^2jO}.
$$
The sum of the two branches is invariant under $\sigma$ coefficientwise at each power, since the quadratic defining them has rational coefficients.

Over $\mathbb Q_p(i,d)$, define the formal series
$$
 L_K=\log K(x,y)-p^{-1}\log K(x^p,y^p).
$$
It lies in $\mathbb Z_p[[x,y]]$ since $K^p/K(x^p,y^p)$ is $1\bmod p$, and its constant coefficient is zero. For $j>0$, use the exact factorisation
$K(x,y)=T(x)(1-yY_1(x))(1-yY_2(x))$. It gives
$$
 [y^j]\log K=-\frac{Y_1(x)^j+Y_2(x)^j}{j}.
$$
At bidegree $(qi,qj)$ with $i,j>0$, the coefficient of $L_K$ is thus $-1/(qj)$ times the sum of the two differences computed above. It belongs to $qO$, hence to $q\mathbb Z_p$ since it is rational and the extension is unramified. On either coordinate axis, the logarithm is $\log T(z)=\log(1-z^3)-\log(1-z)$. Its reduced logarithm vanishes at every positive degree divisible by $p$, since $p\ne3$.

Consequently there exist $H_x,H_y\in\mathbb Z_p[[x,y]]$ such that
$$
 L_K=D_x H_x+D_y H_y,\qquad D_x=x\partial_x,\quad D_y=y\partial_y.
$$
Indeed at each nonconstant bidegree $(h,k)$, divide its coefficient by the nonzero index with smaller $p$-adic valuation, using the sole nonzero index on either axis. The divisibility just proved supplies the denominator whenever both indices are multiples of $p$; coefficients with a unit index already lie in $\mathbb Z_p$.

## 4. The walk congruence

Let $q=p^r$. Set $C=K(x^p,y^p)^{nq/p}$. Both $D_xC$ and $D_yC$ are multiples of $nq$, by differentiation. The first-order expansion as in §3 gives
$$
 K(x,y)^{nq}=C\exp(nq L_K)\equiv C+nq\,C L_K\pmod {q^2}.
$$
At bidegree $(nq,nq)$, the coefficient of $C D_xH_x$ is divisible by $q$: it equals the corresponding coefficient in $D_x(CH_x)-H_xD_xC$. The same holds for $D_y$. Thus the correction vanishes modulo $q^2$. By §1 the coefficient on the left is $a(nq)$, and the coefficient in $C$ is $a(nq/p)$. This proves the theorem for every positive $n,r$. In fact the identical argument compares coefficients at any bidegree whose two indices are divisible by $q$.

## Verification and attribution

Independent checks within the same research session examined the parametrisation, good reduction at inert primes, the signs in the lift comparison, the integrated denominators, the Frobenius permutation of branches and both coefficient transfers. They are checks by computational agents, not external peer review.

A separate exact-integer computation checked 183,067 prime-divisor comparisons through index 100,000. Some comparisons attained exactly the predicted valuation at each depth $1,\ldots,7$. These are checks on the proof and cannot replace its universal quantifiers.

Liu and Yeh’s related paper treats divisibility for walks of odd prime length; its abstract does not state the all-depth congruence. [Liu and Yeh, Enumeration and Divisibility of Higher Dimensional King Walks (2025)](https://doi.org/10.1017/S0004972725100373)

Bala’s note, the OEIS record, indexed literature and preprints, Zenodo, public repositories and upstream submissions were searched. No earlier proof of this particular conjecture was found in the sources checked. The methods of Schwarz, Vologodsky and Walcher predate this application. A public research timestamp, an official Lean verdict and tracker attribution are separate events.
