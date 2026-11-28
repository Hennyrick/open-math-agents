# A094061: the "tangential" route (chosen formalisation route)

This is a refinement of the manuscript `../PROOF.md`. That manuscript is a mathematical argument by
GPT-6.2 Astra for Hennyrick, applying the dilogarithmic Frobenius regulator of Schwarz–Vologodsky–Walcher
to Bala's conjecture. The overall architecture is unchanged: branches, a Steinberg calculation, and two
coefficient transfers. Only the Steinberg decomposition is re-chosen, so that every Steinberg pair is
*tangential at the base point*. That removes the unit-argument dilogarithm and the rational
representatives `D_h` from the proof. The refinement, the analysis and the checks below are by Claude
(Claude Code session). The whole chain is not yet formally verified.

## Setting
p >= 5, F = Q(w) with w^2+w+1 = 0, O = Z_(p)[w], and sigma the automorphism with sigma(w) = w^p.
R = O[[z]], D = z d/dz, phi(h)(z) = h^sigma(z^p).
DR = { h : [z^N]h is in N*O for all N >= 1, constant term 0 }.
For g = zeta z^k u (zeta a root of unity, u in 1+zR): lambda(g) = Dg/g, L(g) = phi(lambda g),
U(g) = log u - p^-1 phi(log u). U(g) is integral, formal, with constant term 0.
For a constant kappa in O^x, U(kappa) = p^-1 log(kappa^p / sigma kappa). This is the only p-adic quantity
in the proof. It can be replaced by a truncated sum at any finite precision.
E(f,g) = U(f) lambda(g) - U(g) L(f). E is bilinear, and E(f,g)+E(g,f) = D(U(f)U(g)).

## Steps
0. Bridge: a(N) = [x^N y^N] K^N, with K = (1+x+x^2)(1+y+y^2) - xy.
1. Curve: the conic u^2+v^2 = -2 (u = (1-X)/(1+X), v = (1-Y)/(1+Y)) has the F-point (1, sqrt(-3)),
   which corresponds to (X,Y) = (0, w^2). Parametrisation over F:
   X(m) = (1+sqrt(-3) m)/(m(m - sqrt(-3))),
   Y(m) = ((1+sqrt(-3))m^2+2m+(1-sqrt(-3)))/((1-sqrt(-3))m^2-2m+(1+sqrt(-3))).
   K(X(m),Y(m)) = 0 identically (`param.py`). Base point m0 = -1/sqrt(-3).
   X has zeros {m0, oo} and poles {0, sqrt(-3)}. Y has zeros {-1, -w^2} and poles {1, -w}, up to the
   choice of w.
   The values of X at the zeros and poles of Y, and of Y at those of X, are roots of unity. All
   differences of these points have norms of the form 2^a 3^b, so they are p-units for p >= 5.
2. Branch: m(z) in O[[z]] with X(m(z)) = z and m(0) = m0. Y(z) := Y(m(z)), so Y(0) = w^2.
   Core Proposition: U(Y) is in DR.
3. Section 3 of the manuscript: Core Proposition => KEY, using Y_2 = 1/Y_1 and
   log K = log T(x) + log(1-yY_1) + log(1-yY_2).
4. Section 4 of the manuscript: KEY => a(n p^r) = a(n p^(r-1)) mod p^(2r).

## Proof of the Core Proposition
Choose a coordinate in which all special points are finite. Write m_a and n_b for the orders of X and Y.
Then sum_a m_a = 0, m_{m0} = 1 and sum_b n_b = 0. Normalise: e0 = (m(z)-m0)/kappa0, where kappa0 is the
leading coefficient, so e0 = z(1+...). For every other point, e_a = (m(z)-a)/(m0-a), which has constant
term 1. Then z = e0 * prod_{a != m0} e_a^{m_a} exactly, and Y = w^2 prod_b e_b^{n_b}.
For a != m0 and b in B, take the tangential pair f_ab = kappa_ab e0/e_a, so that 1 - f_ab = e_b/e_a exactly.
Here kappa_ab = kappa0 (b-a)/((m0-a)(b-m0)).
Tangential Steinberg lemma => E(f_ab, 1-f_ab) is in DR. Expanding bilinearly:

    E(e_a,e_b) = E(e0,e_b) - E(e0,e_a) + U(kappa_ab)(lambda_b - lambda_a)   mod DR.

Summing with weights m_a n_b gives E(z,Y) = C mod DR, where

    C = sum_b n_b lambda_b U(prod_a kappa_ab^{m_a}) - sum_a m_a lambda_a U(prod_b kappa_ab^{n_b})
      = sum_b n_b lambda_b U(X(b)) - sum_a m_a lambda_a U(Y(a)/Y(m0)) = 0,

because the boundary values are roots of unity. Since E(z,Y) = -U(Y), U(Y) is in DR.

## Tangential Steinberg lemma
Let f = kappa z u, kappa in O^x, u in 1+zR. Then E(f,1-f) = D(H) with H integral. Formally,
H = Li2(f) - p^-2 phi(Li2 f) + U(f) log(1-f). Put v = zu, t1 = log(phi u / u^p) = -p U(u), and
rho = sigma(kappa)/kappa^p. A formal Taylor expansion of Li2(phi f) in t1 gives

    H = [Li2(kappa v) - p^-2 Li2(sigma(kappa) v^p) + U(kappa) log(1-kappa v)]
        + U(u) [log(1-kappa v) - p^-1 log(1-sigma(kappa) v^p)]
        - sum_{k>=2} (-1)^k p^{k-2} U(u)^k R_{k-2}(sigma(kappa) v^p)/k! ,   with R_j(w) = sum n^j w^n.

- The second and third groups are integral (p >= 5).
- In the first group, the coefficient of v^n is integral for p not dividing n. At n = pm it equals
  kappa^{pm} (1 - rho^m + m log rho)/(p^2 m^2), which is integral because
  v(1 - rho^m + m log rho) >= 2(1+v(m)).

Checked numerically for kappa in {2, 3, 1/2, 6}, p in {5, 7}. Omitting U(kappa) breaks integrality
exactly at multiples of p (`hkappa.py`).

## Cost comparison (summary)
- Manuscript as written: Q(i, sqrt 3), unit-argument Steinberg pairs with arbitrary constants,
  D_h approximants with an injectivity argument in a completed localisation, and the homotopy integral
  with p-adic convergence. Heaviest.
- Tangential route (this file): Q(w) only, tangential pairs only, formal Taylor expansion, and p-adic
  logs of 12 constants via truncated sums. Cheapest guaranteed route.
- Purely algebraic two-variable route (`NOTES.md`): no field extension or constants, but it needs a
  missing relation. Searches with 339 Steinberg pairs, rational constants included, did not find it.
  The obstruction behaves like the Bloch-group class [-w] of a sixth root of unity, which rational
  origin-normalised relations cannot produce. Abandoned.
