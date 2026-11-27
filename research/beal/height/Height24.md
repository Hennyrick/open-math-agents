# Beal's conjecture through height 16,777,216

`BealHeight.TwoTo24.checked` proves that if positive integers satisfy
$A^x+B^y=C^z$, all three exponents exceed two, and $C^z ≤ 2^{24}$,
then $\gcd(A,\gcd(B,C))>1$.

Run `./check-height24.sh` in this directory with Lean 4.33.1 on the path.
Set `LEAN` to an absolute Lean executable to select it explicitly. Only Lean's
standard library is required. The script builds at most three row modules at
once, caches the checked modules in `.height24-build`, and prints the
theorem's type and axioms. To replay all proofs from source, set
`BEAL_HEIGHT_BUILD` to a new empty directory.

`Bounded.lean` proves that the finite check is equivalent to the bounded
statement, including arbitrary exponents for base one. `Height24/Data.lean`
stores 406 pairs of bases and power values in 51 blocks. They represent 355
distinct values. `Height24/Enumeration.lean` proves that the block list is
exactly the complete enumeration. `Height24/Rows0.lean` through
`Height24/Rows6.lean` check all ordered pairs of entries by kernel computation.
For each sum the check tests every base representing that sum.
`Height24.lean` combines the blocks and applies the equivalence.
