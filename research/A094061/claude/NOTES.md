# A094061: working notes (Claude Code session, continuing Hennyrick's line)

Status: research in progress. No Lean proof yet. Nothing here is a verified result unless stated.
The earlier session's Lean files did not survive; only `../PROOF.md` (commit c00fca0) did.

## Notation
- `K(x,y) = T(x)T(y) - xy`, `T(z) = 1+z+z^2`; `a(N) = [x^N y^N] K^N`.
- `s = x/(1+x)^2`, `t = y/(1+y)^2`. Exact identity: `K = (1+x)^2 (1+y)^2 (1 - s - t)`. Put `G = 1 - s - t`.
- `phi`: `x -> x^p, y -> y^p`. For `F` in `1 + (x,y)Z[[x,y]]`: `L_F = log F - p^-1 phi(log F)`.
- `E = D_x R + D_y R` (R = Z_(p)[[x,y]]) = series whose `(h,k)` coefficient is divisible by `p^min(v_p h, v_p k)`.

## Reductions (checked numerically, argued on paper)
1. KEY: `L_K` lies in `E` for p >= 5. KEY implies the theorem via manuscript section 4.
   Equivalent: the exponents in `K = prod (1 - x^h y^k)^c(h,k)` satisfy `p^v_p(gcd(h,k)) | c(h,k)`.
   Checked to degree 40 (`expo.py`); fails at p = 2, 3.
2. `L_{(1+x)^2(1+y)^2}` lies in `E`, so KEY is equivalent to `L_G` lying in `E`.
3. Branch form (manuscript section 2): `lambda = xY'/Y = c * x(1-x)/((1+x+x^2) sqrt(1+2x/3+x^2))`, with
   `c = +-1/sqrt(-3)`. `U(Y)` in `DR` is equivalent to
   `[x^{pn}]g = (p/3)[x^n]g mod p^{2(1+v_p n)}` for `g = x(1-x)/((1+x+x^2)sqrt(1+2x/3+x^2))`.
   Checked to N = 400, p <= 23, and sharp (`s1.py`).
4. Factorwise KEY fails (for example for `1 - s t`); only the full line `1 - s - t` works (`key.py`).

## Two-variable regulator approach (new)
For normalised units and coordinates f, g, h (constant term 1, or a monomial times such), define
`U(f) = L_f`, `phi'f = phi^*(dlog f)/p` and

    R(f,g,h) = U(f) dlog g ^ dlog h - U(g) phi'f ^ dlog h + U(h) phi'f ^ phi'g .

- `R(x,y,F) = U(F) = L_F`, so KEY is equivalent to `R(x,y,G) = 0 mod E`.
- R is multilinear, and alternating modulo exact forms with integral potentials (checked by hand:
  `R(f,g,h)+R(g,f,h) = d(U_f U_g dlog h)`, `R(f,g,h)+R(f,h,g) = d(U_g U_h phi'f)`).
- Steinberg: `R(h,1-h,c) = d(H(h) dlog c)`, where `H(h) = Li2(h) - p^-2 phi(Li2 h) + U(h) log(1-h)`.
- Integrality lemma: for `h = monomial * u` with `u(0)=1` and p >= 5, `H(h)` is p-integral. Proof sketch:
  `phi h = h^p (1+theta)` with `theta` in `pR` and `(x,y)`. Taylor-expand `Li2(w e^t)` at `w = h^p`, `t = -pU`. This gives
  `H = sum_{p∤n} h^n/n^2 - U sum_{p∤n} h^n/n - sum_{k>=2} (-1)^k p^{k-2} U^k R_{k-2}(h^p)/k!`,
  with `R_j(w) = sum n^j w^n`. Every term is integral and the sum converges formally. No p-adic limits are needed.
  Checked numerically (`hint.py`).
- In one variable, `E(1+z, 1+z+z^2)` is exact. It follows from the single five-term pair
  `f = z(1-z^2)/(1-z^3)`, `1-f = (1-z)/(1-z^3)` (`e1d.py`, `wedge.py`).
- Linear algebra over these Steinberg relations (`wedge.py`, `la.py`) gives
  `{x,y,G} = 4{1+x,1+y,G}` modulo relations. Remaining obstruction: `Z = {1+x,1+y,G}`.
  The curve `K = 0` has an acnode at (-1,-1) with tangents of slope +-i.
  So far the normalised rational pairs found (`pairs1.txt`) do not span Z.
