# Prime factors of the right-hand base in the cyclotomic CM case

Let $X^5+Y^3=Z^p$ be a primitive integer solution with $XYZ\ne0$. Let $K=\mathbf Q(\sqrt5)$, $M=\mathbf Q(\zeta_5)$, and write $\chi_5(n)=(n/5)$ for the quadratic character modulo 5. Assume Jaswal's inputs (LL), (EL), (T2.1), (P7.4)(a) at 3, and (Ex₀), as in his Theorem 6.15. Let $p$ be a prime outside his exceptional set
$$
\mathcal P=\{2,3,5,7,11,13,19,29,31,41,61,71,79,89,101,109\}
$$
and assume $p\not\equiv1\bmod5$.

**Claim.** If $5\mid X$, then $\gcd(Z,30p)=1$, and every rational prime $\ell\mid |Z|$ satisfies
$$
\begin{array}{c|c}
\ell\bmod5&\text{necessary congruence}\\ \hline
1 &\ell\equiv1\bmod p\\
4 &\ell\equiv-1\bmod p\\
2,3 &\ell^2\equiv-1\bmod p .
\end{array}
$$
In particular $\ell^2\equiv\chi_5(\ell)\bmod p$ in all cases, so
$$
                  Z^2\equiv\chi_5(Z)\pmod p .
$$
If also $p\equiv3\bmod4$, then every prime factor of $|Z|$ is either $1$ or $-1$ modulo $5p$. Consequently $Z\equiv\pm1\bmod 5p$ and each such factor is at least $10p-1$. The direct-$J_0$ case follows from the paragraph after Jaswal's Theorem 6.15; extension to every unit class of $Y$ uses his classification of the relevant CM newforms in Lemma 6.11. [Primary source](https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf)

## The form and its integral CM action

First suppose $5\mid X$ and $Y\equiv\pm1,\pm3,\pm4,\pm7\bmod25$. The paragraph following Theorem 6.15 and Table 7 give $6\mid X$ and a direct residual congruence to the newform of $J_0=\operatorname{Jac}(V^2=U^6+12U)$. In particular $\gcd(Z,30)=1$. The integral automorphism
$$
 \alpha(U,V)=(\zeta_5U,\zeta_5^3V)
$$
gives $\mathbf Z[\alpha]\simeq\mathbf Z[\zeta_5]=\mathcal O_M$. Its endomorphisms are defined over $M$. The authors' chosen real multiplication is the real subring by Lemma 2.5(a), whose proof also shows that the rational $\mathfrak p$-adic Tate module is rank one over $M\otimes_K K_{\mathfrak p}$. Here $\mathfrak p$ is a coefficient prime of $K$ above $p$. [Jaswal, Proposition 2.2, Lemma 2.5(a), Definition 4.4 and Theorem 6.15](https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf)

Because $p\not\equiv1\bmod5$, the place $\mathfrak p$ is inert in $M/K$. For $p\equiv4\bmod5$ its residue field $k$ is $\mathbf F_p$ and that of $M$ is $k_2=\mathbf F_{p^2}$. For $p\equiv2,3\bmod5$ the two residue fields are $k=\mathbf F_{p^2}$ and $k_2=\mathbf F_{p^4}$. The local extension is unramified quadratic in both cases. The $\mathfrak p$-adic integral Tate lattice is stable under the full local CM order. It is torsion-free of rank one over this discrete valuation ring, hence free of rank one. Its reduction $J_0[\mathfrak p]$ is one-dimensional over $k_2$. The elements of $G_M$ commute with this action and thus act by multiplication in $k_2^\times$.

For completeness, the field-multiplication property also holds for every CM candidate arising when $5\mid X$. By Proposition 6.4 the reducible branch would force $30\mid Z$, contrary to primitivity. In Lemma 6.7 the special parameters require $5\nmid XYZ$ by Theorem 1(a). The $K(\sqrt{-3})$ branch of Proposition 6.6 would give $5\mid Y$. Thus the candidate has CM by $M$ and $6\mid X$, $5\nmid YZ$. Section 6.4 justifies the use of Lemma 6.7 under the named inputs. Lemma 6.2(a) gives $\varepsilon_3=2$ since $3\mid X$, and $\varepsilon_5\in\{2,3\}$ by Lemma 6.7. Lemma 6.11 classifies *every* parallel-weight-two trivial-character CM newform at these levels as $G_J$ or $G_J^\sigma$, with $J$ a Jacobian of $V^2=U^6+12cU$ or its quadratic twist by $-3$ and $c\in\{1,3,9,27,81\}$. Each carries the same integral order-five automorphism over $M$, with rational CM Tate module of relative rank one, as it is geometrically isomorphic to $J_0$. A quadratic twist acts on the representation by scalars. Coefficient conjugation replaces the chosen coefficient prime by its conjugate or the residue field by its conjugate identification. It preserves field multiplication over a quadratic extension of $k$ and fixes the prime-field scalars used below. These facts explain why the proof is valid for the full CM list without identifying an individual form when $Y$ lies outside the direct-$J_0$ classes. [Jaswal, §6.4 and Lemma 6.11](https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf)

## The coefficient prime

If $p\mid Z$, the Frey Jacobian has multiplicative reduction of toric rank two at a place $v$ of $K$ above $p$, by (T2.1), stated in Jaswal's Theorem 2.8. On the maximal unramified extension the torus splits. Its Tate uniformization gives semisimplified inertia characters $\bar\chi_p,\bar\chi_p,1,1$ on the full $p$-torsion, where $\bar\chi_p$ is the cyclotomic character. The two-dimensional constituent has determinant $\bar\chi_p$, so its characters must be $1,\bar\chi_p$. These differ since $K_v/\mathbf Q_p$ is unramified and $p>5$.

On the other hand the matching CM representation is induced from $G_M$. The decomposition group at $v$ meets $G_M$ in the index-two subgroup of the unramified quadratic $M_w/K_v$. Its two inertia characters after reduction and scalar extension are $\tau,\tau^{\mathrm{Fr}}$ for a lift of Frobenius. If one is trivial then both are trivial. This contradicts the calculated inertia characters and proves $p\nmid Z$. This argument applies at $p$ itself without using the good-prime trace formula there. [Jaswal, Lemma 2.5 and Theorem 2.8](https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf) · [Supplement, Proposition S1.14](https://zenodo.org/api/records/23149238/files/jaswal-x5y3zp-supplement.pdf/content)

## Frobenius at a divisor of $Z$

Every $\ell\mid |Z|$ is now outside $30p$. Write $\lambda\mid\ell$ in $K$, $q=N\lambda$, and $g=\operatorname{Frob}_\lambda$ for arithmetic Frobenius. The level-lowering formula (40) gives residual trace $\delta(1+q)$, where $\delta\in\{1,-1\}$, and the cyclotomic determinant gives $\det(g)=q$ in $k$. If $\ell\equiv1\bmod5$, then it splits completely in $M$, $q=\ell$ and $g\in G_M$. On the CM module its characteristic polynomial equals
$$
               (T-\delta)(T-\delta\ell).
$$
It splits over $k$. A multiplication operator from $k_2^\times$ with a $k$-eigenvalue is scalar: if $av=bv$ for $v\in k_2^\times$ and $b\in k$, then $a=b$. Thus its two eigenvalues coincide and $\ell\equiv1\bmod p$. The possible sign in (40) does not affect this conclusion. [Pacetti–Villagra Torcomian, §7.4.3, formula (40)](https://arxiv.org/html/2512.17845v1#S7.SS4.SSS3)

If $\ell\equiv4\bmod5$, then $q=\ell$ and $\lambda$ is inert in $M/K$. The induced trace vanishes, so (40) gives $\ell\equiv-1\bmod p$. If $\ell\equiv2,3\bmod5$, then the residue degree over $\mathbf Q$ is two, $q=\ell^2$, and again $\lambda$ is inert in $M/K$ because $\ell^2\equiv-1\bmod5$. This time (40) gives $\ell^2\equiv-1\bmod p$.

Multiplication of the squared congruences with multiplicities gives $Z^2\equiv\chi_5(Z)\bmod p$, also for negative $Z$ since $\chi_5(-1)=1$. When $p\equiv3\bmod4$ the third row has no solution. In the first two rows the residues of $\ell$ match the same sign modulo 5 and modulo $p$, hence modulo $5p$ by the Chinese remainder theorem. An odd prime of that form is at least $10p-1$, since $5p-1$ and $5p+1$ are even. Multiplication, with the sign of $Z$ if necessary, gives $Z\equiv\pm1\bmod5p$.

## Positive solutions with $3,5\nmid C$

Let $A^5+B^p=C^3$ be primitive with $\gcd(B,30)=1$ and $\gcd(C,15)=1$, under the same five inputs and $p\notin\mathcal P$ (in particular for $p>109$). The CM conclusions here do not require $5\mid A$. Put $(X,Y,Z)=(A,-C,-B)$. Reducibility is excluded by Proposition 6.4, since it would give $30\mid Z$. In Lemma 6.7 a special-parameter congruence would imply $3\mid Y$ by Lemma 6.8, whose final assertion uses (P7.4)(a) at 3 and Lemma 6.18(d). A congruence with the $K(\sqrt{-3})$ CM branch would imply $5\mid Y$ by Proposition 6.6(b). Thus the only possibility is the cyclotomic CM branch, with $6\mid X$ and level dividing $3^2(\sqrt5)^3$. Lemma 6.11 applies as above. No separate assumption of Pacetti–Villagra Torcomian's Theorem 7.18 is needed. For $p\not\equiv1\bmod5$, the prime-factor table and $B^2\equiv\chi_5(B)\bmod p$ follow for every such solution. [Jaswal, §§6.4 and 6.7, especially Lemmas 6.8 and 6.18(d)](https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf)

Suppose also $5\nmid A$ and set $t=A^5/C^3\bmod25$. Theorem 6.25(a) gives $t\in\{2,3,4,8,13,18,23\}$, and Theorem 1(b) excludes CM for $3,8,13,23$. Hence $t\in\{2,4,18\}$. For every $p\equiv3\bmod4$ outside $\mathcal P$ one has $\chi_5(B)=1$: primes of $B$ outside $30p$ nonsquare modulo 5 would require $\ell^2\equiv-1\bmod p$, while the factor $p$ itself is either a square modulo 5 or excluded by the coefficient-prime argument. Reduction of $B^p=C^3(1-t)$ modulo 5 gives $\chi_5(C)=\chi_5(1-t)$. Thus $C$ is a square modulo 5 when $t=2$, and a nonsquare modulo 5 when $t=4$ or $18$. This last sign test includes $p\equiv1\bmod5$. [Jaswal, Theorems 1(b) and 6.25(a)](https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf)

For the positive-base equation $A^5+B^p=C^3$, the conclusion reads $p\mid B^2-\chi_5(B)$. In particular, for each fixed $B>1$ in the stated mixed family, the surviving primes $p\not\equiv1\pmod5$ outside the exceptional set divide the explicit nonzero integer $B^2-\chi_5(B)$. This gives a finite, effectively computable list of exponents for that base. The arithmetic step from individual prime factors to their product, including multiplicities, has been checked in Lean. [Lean certificate](CartanProduct.lean)
