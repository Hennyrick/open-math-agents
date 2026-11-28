# How many points can replace deleted ternary points?

This note concerns three-term arithmetic progressions with positive difference in the integers. Let $I_m=\{0,\ldots,3^m-1\}$, let $K_m$ consist of the integers in this interval whose ternary digits belong to $\{0,2\}$, and let $A\subseteq I_m$ be progression-free. Write $t=|K_m\setminus A|$ and $h=|A\setminus K_m|$. The set $K_m$ has $2^m$ elements and is progression-free. All other integer sites are available to $A$.

## Three counting bounds

* For every $m$ and $t$, $h\,2^m\le 2t\,3^m$. The theorem `ParityMass.integer_stability` proves this directly for finite sets of integers represented by `Fin (3^m)`.
* The more local bound $h\le m t + \sum_{\{u,v\}\subseteq D}(1+m-d(u,v)) \le m t(t+1)/2$ is useful for small $t$. Here $D$ is the set of missing binary words and $d$ denotes Hamming distance. A proof follows below.
* When exactly one core site is missing, the largest possible size of $A$ is exactly $2^m-1+m$. This formula allows the missing site to be selected freely.

### Encoding integer midpoints by cube faces

Identify each binary word $u$ with the integer $k(u)=2\sum_i u_i3^i$ in $K_m$. For $z\in I_m$, form a face $F(z)$ of the binary cube. A ternary 0 fixes a bit to 0, a 2 fixes it to 1, and a 1 leaves it free. Opposite vertices of this face give an integer pair with midpoint $z$, by addition without carries. Conversely all representations as a midpoint of core sites arise this way, since the sum of the two binary-digit words has no carries. The encoding is one-to-one between ternary integers and cube faces.

When $z\in A\setminus K_m$, its face has positive dimension and $D$ must meet every pair of opposite vertices. For the first bound, each ternary word and auxiliary binary word select an ordered pair of opposite vertices. At a free position use the auxiliary bit to pick the first vertex. At a fixed position both endpoints are forced. For a prescribed first vertex, exactly three choices of the input digit and bit work in each coordinate. This also holds for the second vertex. Each of the $h2^m$ inputs must use at least one of the $t$ deleted vertices. Counting both endpoint orientations gives the stated bound.

For the local bound, consider the deleted vertices $D_F=D\cap F$ in a face of dimension $j\ge1$ corresponding to an occupied extra site. If two deleted vertices are opposite, their smallest containing face is $F$. Otherwise exactly one vertex of each opposite pair is deleted. Walk along edges of $F$ from a deleted vertex to its opposite. On the first edge from a deleted vertex $a$ to an undeleted vertex $w$, the opposite $b$ of $w$ is deleted. The words $a,b$ differ in every free coordinate except the direction of that edge. Their smallest containing face therefore has codimension one in $F$. For $j=1$ the two words coincide.

Each of the $t$ repeated pairs accounts for at most $m$ edges. For two distinct deleted words at distance $d$, their smallest face has dimension $d$. It determines at most $1+m-d$ possible faces, counting itself and the faces obtained by freeing one of its other coordinates. Summing gives the local bound. The opposite-pair argument is formalised in `ParityFace.antipodal_or_near`.

### Sharp construction with one missing point

The local bound with $t=1$ gives $h\le m$. To attain it, choose a word $u$ whose bits alternate by coordinate, and delete $v=k(u)$. For every $i=0,\ldots,m-1$, add the midpoint $y_i=v+(1-2u_i)3^i$ of the edge from $u$ in direction $i$. Each $y_i$ lies in the interval, is odd, and has only one representation as the midpoint of two core sites. That representation uses $v$. The $y_i$ are distinct.

The signed offsets $(1-2u_i)3^i$ are all equal modulo 4, so any two added points have an odd midpoint. Thus a pair of added points cannot have a retained core site as its midpoint. Three distinct added points cannot form a progression. In the equation with coefficients $1,-2,1$ on their signed offsets, the smallest power of 3 appears exactly once and its coefficient is a unit modulo 3. These cases exhaust all possible progressions. The resulting set has $2^m-1+m$ members.

### All choices of the missing point

For a specified deleted word $u$, the only candidate extra sites are the $m$ edge midpoints $y_i$ above. Their pairwise conflicts form an explicit forest on the indices. For each $i$, look rightward for the **first** $j>i$ with $u_j=u_{j-1}$. If it exists, join $i$ to $j$. These are all the edges. A set of candidate sites can be adjoined exactly when its indices are independent in this forest. In particular, a hole permits all $m$ additions exactly when its digits alternate.

To see the edge rule, put $s_\ell=1-2u_\ell$. An even core midpoint $k(a)$ of $y_i,y_j$ would satisfy
$$
4\sum_\ell (a_\ell-u_\ell)3^\ell=s_i3^i+s_j3^j .
$$
Below position $i$ the bits must agree, by reduction modulo 3 one digit at a time. At $i$, reduction modulo 3 forces $a_i-u_i=s_i$ since the only possibilities are 0 and $s_i$. Subtracting $4s_i$ and dividing by 3 leaves the residual sign $-s_i$ at the next digit. At each intermediate digit this forces the sign to alternate again. A mismatch is impossible by reduction modulo 3. At position $j$, the incoming sign and $s_j$ must cancel. If they were equal, their sum would be $2s_j$, which is congruent to neither permitted difference $0,s_j$ modulo 3. Cancellation occurs exactly when $u_j=u_{j-1}$ after an alternating stretch. In that case taking all higher bits unchanged gives a core midpoint, and its bit at $i$ differs from the missing word, so the midpoint is retained. The complete digit equivalence, including all lower and higher positions, is proved in `SingleHole.pair_conflict_iff`.

The argument with the smallest power of 3 rules out triples of added points for arbitrary signs as well. Thus the elementary graph criterion captures every obstruction. Each vertex has at most one edge to a larger vertex, which rules out cycles by considering the smallest vertex of a hypothetical cycle. The usual maximum-independent-set recursion on a forest gives the optimum for any specified missing site in linear time, after computing the next repeat from right to left. Direct integer midpoint checks agreed with this graph for all $16{,}382$ choices across $1\le m\le13$.

### Adding the outer endpoint for an arbitrary one-site deletion

For every $m\ge4$, the sharp one-deletion optimum on the **closed** interval $[0,3^m]$ is $2^m+m$. The half-open upper bound allows at most one further point. To attain it, choose the alternating word starting with low-order bits $1,0,1,0$. Then $v\equiv20\bmod81$, and the odd edge midpoints have residues in $E=\{11,19,20,23,47\}$ modulo 81. The first four coordinates give $19,23,11,47$, and every subsequent coordinate gives 20. Retained core sites reduce into $K_4$ modulo 81.

Write $q=3^m$. In any progression containing $q$, the other endpoint $x$ is odd and is one of the added edge midpoints, and the middle point $y$ is in the original set. The identity $q+x=2y$ gives $x\equiv2y\bmod81$. But $E$ is disjoint from the residues $2(K_4\cup E)\bmod81$, by direct enumeration. This proves attainability after adjoining $q$. The two finite residue sets and the implication permitting the endpoint are checked in `ParityFace.extend_at_multiple_of_81`.

### What changes when zero is the missing point?

On the **closed** interval $[0,3^m]$, retaining the full core permits precisely one extra site, the outer endpoint $3^m$. If zero is deleted and every other core site is retained, all extra sites must belong to $\{1,3,\ldots,3^m\}$. A subset of these powers is permissible exactly when its exponents contain no two consecutive integers. The exact optimum in this case is $2^m-1+\lceil(m+1)/2\rceil$. The classification and its converse are `ParityCarry.all_extras_after_zero` and `ParityCarry.path_criterion`. The cardinality follows by pairing consecutive positions of the path and taking alternate positions.

## Finite checks and interpretation

`Erdos142ParityCarry.lean` checks a 47-element progression-free set in $[0,243]$. This is a restriction and translation of Gavin Theobald's published 91-element set of span 686. See [Wróblewski's database](https://www.math.uni.wroc.pl/~jwr/non-ave.htm). The 47-element witness is a lower bound on the unrestricted optimum.

`Parity244.cpp` enumerates every deletion mask of the requested size in the 32-element core $K_5$. Each live candidate initially avoids a progression with two retained points. Including a candidate updates this condition for every remaining site. The depth-first search includes every compatible subset unless its upper bound is already attained. Groups of pairwise incompatible candidates give the upper bound of one choice per group. The program separately verifies that its reported witness has the requested intersection and contains no progression.

The search gave the following exact maxima.

| Core points omitted | Deletion masks checked | Largest set |
| ---: | ---: | ---: |
| 0 | 1 | 33 |
| 1 | 32 | 37 |
| 2 | 496 | 40 |
| 3 | 4,960 | 41 |
| 4 | 35,960 | 43 |
| 5 | 201,376 | 43 |
| 6 | 906,192 | 44 |
| 7 | 3,365,856 | 44 |

To reproduce every row, compile with `g++ -O3 -std=c++20 Parity244.cpp -o parity244` and run `./parity244 7`. Each output line includes a realising set. A second search without the clique-cover bound independently reproduced the rows through six omissions. Therefore a 47-point set must omit at least eight of the 32 canonical even sites. The reflected odd core has the same property under the bijection $x↦243-x$.

The global mass bound, the classification after deleting the site zero, and the 47-point witness have Lean proofs. The sharp one-deletion count and the local counting bound above have written proofs. The finite maxima use exhaustive C++ search. None of these results identifies the asymptotic order of the unrestricted extremal function in Erdős #142.
