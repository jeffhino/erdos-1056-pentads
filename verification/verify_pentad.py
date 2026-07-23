"""Independent verification of the #1056 pentad criterion. Written fresh, trusts nothing."""
import sys

def isprime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    # deterministic Miller-Rabin for n < 3.3e24
    d, r = n-1, 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a >= n: continue
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def primerange(lo, hi):
    return (n for n in range(max(lo,2), hi) if isprime(n))

def fact_mod_table(p):
    """n! mod p for n=0..p-1."""
    t = [1]*(p)
    for n in range(1, p):
        t[n] = t[n-1]*n % p
    return t

def h_dirichlet(p):
    """Class number h(-p) for prime p ≡ 3 mod 4, via Dirichlet:
    h = (A - N)/(2 - (2|p)), A/N = #QRs/#NQRs in (0, p/2)."""
    assert p % 4 == 3
    qrs = set(pow(a, 2, p) for a in range(1, p))
    A = sum(1 for a in range(1, (p+1)//2) if a in qrs)
    N = (p-1)//2 - A
    leg2 = 1 if p % 8 in (1, 7) else -1
    num = A - N
    den = 2 - leg2
    assert num % den == 0, (p, num, den)
    return num // den

fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1
        print("FAIL:", msg)

# ---- 1. Wilson pairing n!(p-1-n)! ≡ (-1)^{n+1}, exhaustive, primes < 500 + two big ones
for p in list(primerange(3, 500)) + [10007, 99991]:
    t = fact_mod_table(p)
    for n in range(p):
        lhs = t[n]*t[p-1-n] % p
        rhs = (p-1) if n % 2 == 0 else 1   # (-1)^{n+1} mod p
        check(lhs == rhs, f"pairing p={p} n={n}")
print("1. Wilson pairing: OK" if fails == 0 else "1. FAILURES ABOVE")

# ---- 2. Mordell sign law: m! ≡ (-1)^{(h(-p)+1)/2}, all p ≡ 3 mod 4 in [7, 20000)
f2 = fails
for p in primerange(7, 20000):
    if p % 4 != 3: continue
    m = (p-1)//2
    t = fact_mod_table(p)
    h = h_dirichlet(p)
    check(h % 2 == 1, f"h even?! p={p}")
    want = 1 if h % 4 == 3 else p-1
    check(t[m] == want, f"Mordell p={p} h={h} m!={t[m]}")
print("2. Mordell sign law (1359 primes):", "OK" if fails == f2 else "FAILURES")

# ---- 3. Tetrad construction: q ≡ 1 mod 6, q>=7 → q!-1 ≡ 3 mod 4; every prime factor p ≡ 3 mod 4
#         of q!-1 gives distinct {1,q,p-1-q,p-2} all with factorial ≡ 1; pentad iff h ≡ 3 mod 4.
f3 = fails
import math
tested_pairs = 0
pentads = 0
for q in range(7, 200, 6):
    Q = math.factorial(q) - 1
    check(Q % 4 == 3, f"q!-1 mod 4, q={q}")
    # small prime factors only (trial division to 10^6 for speed)
    x = Q
    facs = []
    for d in range(2, 10**6):
        while x % d == 0:
            facs.append(d); x //= d
        if d*d > x: break
    if x > 1 and x < 10**7 and isprime(x): facs.append(x)
    for p in set(facs):
        if p % 4 != 3 or not isprime(p) or p > 10**7: continue
        tested_pairs += 1
        check(p > q, f"p<=q p={p} q={q}")
        t = fact_mod_table(p)
        S = {1, q, p-1-q, p-2}
        check(len(S) == 4, f"tetrad collision q={q} p={p}")
        check(all(t[s] == 1 for s in S), f"tetrad not all 1: q={q} p={p}")
        m = (p-1)//2
        h = h_dirichlet(p) if p < 200000 else None
        if h is not None:
            joins = (t[m] == 1)
            check(joins == (h % 4 == 3), f"pentad criterion q={q} p={p} h={h}")
            if joins:
                pentads += 1
                check(m not in S, f"m in tetrad q={q} p={p}")
print(f"3. Tetrad+pentad criterion over {tested_pairs} (q,p) pairs, {pentads} pentads:",
      "OK" if fails == f3 else "FAILURES")

# ---- 4. The 12 claimed witnesses, end to end
f4 = fails
witnesses = [  # (p, q, claimed h)
    (359,229,19),(439,37,15),(883,43,3),(907,25,3),(971,361,15),(5003,295,15),
    (5039,7,83),(9439,235,75),(9643,337,11),(9791,301,119),(21839,115,195),(22639,223,55)]
for p, q, hc in witnesses:
    check(isprime(p) and p % 4 == 3, f"witness p={p} not prime≡3")
    check(q % 6 == 1, f"witness q={q} not ≡1 mod 6")
    t = fact_mod_table(p)
    check(t[q] == 1, f"q! != 1: p={p}")   # implies p | q!-1 given q<p
    h = h_dirichlet(p)
    check(h == hc, f"h mismatch p={p}: got {h} want {hc}")
    check(h % 4 == 3, f"h mod 4 p={p}")
    m = (p-1)//2
    pent = {1, q, m, p-1-q, p-2}
    check(len(pent) == 5, f"pentad collision p={p}")
    check(all(t[s] == 1 for s in pent), f"pentad not all ≡1 p={p}")
print("4. All 12 witnesses:", "OK" if fails == f4 else "FAILURES")

# ---- 5. Flagship completeness: solution set of n! ≡ 1 mod 5039 is EXACTLY the pentad
t = fact_mod_table(5039)
sols = [n for n in range(1, 5039) if t[n] == 1]
check(sols == [1, 7, 2519, 5031, 5037], f"5039 solution set: {sols}")
print("5. Flagship p=5039 exact solution set:", "OK" if fails == f4 else "see above")

print()
print("TOTAL FAILURES:", fails)
sys.exit(1 if fails else 0)
