# A class number criterion for pentads of congruent factorials

Progress on [Erdős problem #1056](https://www.erdosproblems.com/1056)
(Guy, *Unsolved Problems in Number Theory*, A15): for how many consecutive
integer intervals can all products be ≡ 1 (mod p)?

**The problem remains open.** This repository contains a new partial result,
its paper, a Lean 4 formalization of the elementary core, and independent
numerical verification.

## The result

For q ≡ 1 (mod 6), q ≥ 7, and any prime p ≡ 3 (mod 4) dividing q!−1 (such p
always exists), the four residues 1, q, p−1−q, p−2 are pairwise distinct with
all factorials ≡ 1 (mod p) — the tetrad of Agustín-Aquino & Hernández
Santiago. Our theorem: the central residue m = (p−1)/2 joins them — five
equal factorials, hence k = 4 consecutive intervals — **if and only if the
class number of ℚ(√−p) satisfies h(−p) ≡ 3 (mod 4)**.

Flagship instance: p = 5039 = 7!−1, whose complete solution set of
n! ≡ 1 (mod 5039) is exactly the pentad {1, 7, 2519, 5031, 5037}, with
h(−5039) = 83.

The paper also proves a multi-seed shape theorem (reducing hexad infinitude
to gcd(q₁!−1, q₂!−1) > 1 infinitely often), a conditional infinitude theorem
for pentad primes, and a limitative theorem explaining why the classical
identity toolkit terminates unconditionally at tetrads.

## Contents

- `paper/` — the note (LaTeX + PDF, 19 pp).
- `lean/` — Lean 4 + Mathlib formalization of the elementary core, **sorry-free
  and kernel-checked** (`#print axioms` shows only `propext`,
  `Classical.choice`, `Quot.sound` for every theorem; no `native_decide`):
  - `WilsonPairing.lean` — n!·(p−1−n)! ≡ (−1)^(n+1) (mod p)
  - `Tetrad.lean` — the tetrad theorem, incl. existence of the p ≡ 3 (mod 4)
    prime factor and the mod-6 distinctness arguments
  - `CentralSign.lean` — the central sign law m! ≡ (−1)^N (mod p), N the
    number of quadratic nonresidues in [1, m] (the novel core)
  - `Pentad.lean` — the pentad criterion (factorial and nonresidue-count forms)
  - `Flagship.lean` — the p = 5039 pentad, center 2519! ≡ 1 computed by the
    Lean kernel itself via `decide`
  - The class-number reading of N (via Mordell 1961 and Dirichlet's counting
    formula) is proved in the paper and *cited*, not formalized.
- `verification/verify_pentad.py` — independent, dependency-free numerical
  verification: Wilson pairing (exhaustive, primes < 500 plus 10007, 99991),
  Mordell's sign law against class numbers for all 1135 primes ≡ 3 (mod 4)
  in [7, 20000), the pentad criterion on constructed (q, p) pairs, all 12
  certified pentads, and the flagship solution set. Runs in ~5 s, zero
  failures.

## Building the Lean project

```
cd lean
lake exe cache get
lake build
```

## Provenance

The mathematics was found and verified with substantial AI assistance
(Claude, Anthropic): parallel proof-search agents, adversarial referee
agents, independent recomputation, and machine formalization, coordinated
and reviewed by the author. Every computational claim in the paper was
replicated at least twice in independently written code; the referee pass
re-derived every proof by hand and authenticated every reference. The tetrad
construction and its Lean development are entirely due to Agustín-Aquino &
Hernández Santiago ([tetrads](https://github.com/octavioalberto/tetrads));
Mordell's theorem is classical. Errors, if any remain, are the author's.

## License

Apache 2.0 (see `LICENSE`). The paper text is © 2026 Jeff Hinojosa.
