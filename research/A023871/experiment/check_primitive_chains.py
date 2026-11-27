"""Independently test the moment, primitive-chain sum, exclusions, and endpoint residues."""
from collections import defaultdict
from math import gcd


def divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def sums(n, p, s):
    m = p**s
    full = filtered = endpoint = 0
    staircase = defaultdict(int)
    endpoints = {}
    ds = [None] + [divisors(j) for j in range(1, n)]
    reverse = 0
    for j in range(1, n):
        for x in ds[j]:
            a = j // x
            for y in ds[n - j]:
                b = (n - j) // y
                if x % p == y % p == 0:
                    continue
                t = a * pow(y, -1, m) % m if y % p else -b * pow(x, -1, m) % m
                assert (t * y - a) % m == (t * x + b) % m == 0
                full += t**4 * x * y
                if x % p and y % p:
                    filtered += t**4 * x * y
                    reverse += a * a * b * b * pow(x * y, -1, m)
                # Tag every tuple with the terminal tuple; compare its sum exactly before reduction.
                u, v, h, k = x, y, a, b
                while h != k:
                    if h > k:
                        v += u
                        h -= k
                    else:
                        u += v
                        k -= h
                staircase[u, v, h, t] += x * y
                if a == b:
                    g = gcd(x, y)
                    poly = ((x + y)**2 - x * y - g**2) // 2
                    endpoints[x, y, a, t] = poly
                    endpoint += t**4 * poly
    assert endpoints == staircase
    assert (full - endpoint) % m == 0
    assert (filtered - reverse) % m == 0
    return full % m, filtered % m


def main():
    cases = 0
    for p, s, ns in [(7, 1, range(1, 22)), (7, 2, range(1, 8)), (7, 3, range(1, 4)),
                     (11, 1, range(1, 16)), (11, 2, range(1, 6)), (13, 1, range(1, 16)),
                     (13, 2, range(1, 4)), (5, 1, range(1,8)), (5, 2, range(1,6))]:
        for k in ns:
            n = k * p**s
            full, both = sums(n, p, s)
            oldfull, oldboth = sums(n // p, p, s - 1) if s > 1 else (0, 0)
            assert (both - full + p * (oldfull + oldboth)) % p**s == 0
            if p >= 7:
                assert full == both == 0
            cases += 1
    print(f'{cases} determinant levels verified, including the p=5 transfer identity')


if __name__ == '__main__':
    main()
