"""Exact finite audits of the Euclidean-chain proof of the A023871 Cartier lemma."""
from fractions import Fraction
from functools import cache
from math import gcd


@cache
def divisorpairs(n):
    return [(x, n // x) for x in range(1, n + 1) if n % x == 0]


def states(N, p):
    for i in range(1, N):
        for x, a in divisorpairs(i):
            for y, b in divisorpairs(N-i):
                if gcd(x, y) % p:
                    yield a, b, x, y


def slope(a, b, x, y, p, m):
    t = (a * pow(y, -1, m) if y % p else -b * pow(x, -1, m)) % m
    assert (t*y - a) % m == (-t*x - b) % m == 0
    return t


def previous(a, b, x, y):
    if x == y:
        return None
    if x < y:
        return a+b, b, x, y-x
    return a, b+a, x-y, y


def successor(a, b, x, y):
    if a == b:
        return None
    if a > b:
        return a-b, b, x, y+x
    return a, b-a, x+y, y


@cache
def probe(N, p, s):
    mod = p**s
    assert N % mod == 0
    all_states = set(states(N, p))
    rest = set(all_states)
    whole = restricted = terminal_sum = total_states = 0
    for head in sorted(z for z in all_states if z[2] == z[3]):
        a, b, g, _ = head
        z = head
        t = slope(*z, p, mod)
        running = 0
        while True:
            rest.remove(z)
            a,b,x,y=z
            total_states += 1
            assert a*x + b*y == N and gcd(x,y) == g
            assert t == slope(*z,p,mod)
            weight = pow(t,4,mod) * x*y
            running += x*y
            whole += weight
            if x % p and y % p:
                restricted += weight
                assert (weight*x*y - a*a*b*b) % mod == 0
            z_next = successor(*z)
            if z_next is None:
                assert a==b
                break
            assert previous(*z_next) == z
            z = z_next
        d = x+y
        assert 2*running == d*d-x*y-g*g
        terminal_sum += t**4 * running
        if d % p:
            assert t==0
        else:
            assert x % p and y % p
            assert (t*x + a)%mod == 0
            assert (2*t**4*running - a**4*(x*x-g*g)*pow(x,-4,mod))%mod == 0
    assert not rest and whole % mod == terminal_sum % mod
    for h, d in divisorpairs(N):
        if d % p:continue
        for g,e in divisorpairs(d):
            if g%p == 0:continue
            units = [k for k in range(1,e) if gcd(k,e)==1]
            assert all(k % p for k in units)
            pp=e
            while pp % p == 0:pp//=p
            pp=e//pp
            assert pp >= p
            for j in (2,4):
                assert sum(pow(k,-j,pp) for k in units)%pp == 0
    assert whole % mod == 0
    if s > 1:
        lower_whole, lower_restricted, _ = probe(N//p,p,s-1)
        assert (whole - restricted - p*(lower_whole+lower_restricted)) % mod == 0
    assert restricted % mod == 0
    # Independent coefficient generation, with rational numbers and no chains.
    def logarithm(k):
        return sum((Fraction(a*a,x) for x,a in divisorpairs(k) if x%p),Fraction())
    coefficients = [Fraction()] + [logarithm(k) for k in range(1,N)]
    actual=sum(coefficients[i]*coefficients[N-i] for i in range(1,N))
    assert actual.denominator % p and actual.numerator % mod == 0
    assert (actual.numerator * pow(actual.denominator,-1,mod)) % mod == restricted % mod
    return whole%mod, restricted%mod, total_states


if __name__ == '__main__':
    pairs=[(7,1,20),(11,1,12),(13,1,10),(17,1,7),(19,1,6),(23,1,6),
           (7,2,12),(11,2,4),(13,2,3),(7,3,2)]
    n_checks=n_states=0
    for p,s,limit in pairs:
        for u in range(1,limit+1):
            _,_,n=probe(p**s*u,p,s)
            n_states+=n
            n_checks+=1
    print(f'{n_checks} exact complete-chain and direct-rational Cartier checks; {n_states} states audited.')
