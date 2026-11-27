"""Probe the Cartier square at prime powers by exact modular arithmetic."""
from math import isqrt
import sys


def primes(bound):
    return [p for p in range(2, bound + 1) if all(p % d for d in range(2, isqrt(p) + 1))]


def residues(p, depth, max_m):
    mod = p ** depth
    size = mod * max_m
    # Fast exact divisor sieve. If n=p^a*u, lambda(n)=p^(2a)*sigma_3(u)/u.
    sigma = [0] * (size + 1)
    for d in range(1, size + 1):
        if d % p == 0:
            continue
        cub = pow(d, 3, mod)
        for m in range(d, size + 1, d):
            sigma[m] += cub
    invs = [0 if i % p == 0 else pow(i,-1,mod) for i in range(mod)]
    ell = [0] * (size + 1)
    for n in range(1, size + 1):
        if n % p:
            ell[n] = sigma[n] * invs[n % mod] % mod
        else:
            ell[n] = p * p * ell[n // p] % mod
    for u in range(1, max_m + 1):
        if u % p == 0:
            continue
        N = mod * u
        v = sum(ell[i] * ell[N-i] for i in range(1, N)) % mod
        yield N, v


def main():
    pmax, depth, max_m=map(int,sys.argv[1:4]);checks=0
    for p in primes(pmax):
        if p < 7:continue
        for n, val in residues(p,depth,max_m):
            checks+=1
            if val: print('failure',p,depth,n,val,flush=True); return
    print('verified',checks,'Cartier coefficients','p <=',pmax,'depth',depth,'unit indices <=',max_m,flush=True)


if __name__ == '__main__':main()
