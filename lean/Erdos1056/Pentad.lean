/-
Copyright (c) 2026 Jeff Hinojosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeff Hinojosa
-/
import Erdos1056.Tetrad
import Erdos1056.CentralSign

/-!
# The pentad criterion

Under the tetrad hypotheses (`p` prime, `q ≡ 1 (mod 6)`, `q ≥ 7`,
`p ∣ q! - 1`) together with the central condition `((p-1)/2)! ≡ 1 (mod p)`,
the five arguments `1, q, (p-1)/2, p - 1 - q, p - 2` are pairwise distinct
and all have factorial `≡ 1 (mod p)`.

By `central_sign`, when moreover `p ≡ 3 (mod 4)` the central condition is
equivalent to the number `N` of quadratic nonresidues in `[1, (p-1)/2]`
being even; `pentad_of_even` packages that form. (The classical reading of
`N` via the class number `h(-p)` — Mordell's `m! ≡ (-1)^{(h(-p)+1)/2}` — is
cited in the accompanying notes but not formalized.)
-/

namespace Erdos1056

open Nat Finset

/-- **Pentad criterion, factorial form.** If `p` is prime, `q ≡ 1 (mod 6)`,
`q ≥ 7`, `p ∣ q! - 1`, and the central factorial satisfies
`((p-1)/2)! ≡ 1 (mod p)`, then the five arguments
`1, q, (p-1)/2, p - 1 - q, p - 2` are pairwise distinct and all have
factorial `≡ 1 (mod p)`. -/
theorem pentad_of_dvd (p q : ℕ) [hp : Fact p.Prime] (hq6 : q % 6 = 1)
    (hq7 : 7 ≤ q) (hdvd : p ∣ q.factorial - 1)
    (hm : ((((p - 1) / 2)! : ℕ) : ZMod p) = 1) :
    List.Pairwise (· ≠ ·) [1, q, (p - 1) / 2, p - 1 - q, p - 2] ∧
      ∀ n ∈ [1, q, (p - 1) / 2, p - 1 - q, p - 2], ((n ! : ℕ) : ZMod p) = 1 := by
  obtain ⟨hqp, ⟨d1, d2, d3, d4, d5, d6⟩, hf1, hfq, hfpq, hfp2⟩ :=
    tetrad_of_dvd p q hq6 hq7 hdvd
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
  have h2m : 2 * ((p - 1) / 2) + 1 = p := by omega
  constructor
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      false_imp_iff, List.Pairwise.nil, and_true, ne_eq, or_false,
      forall_eq_or_imp, forall_eq, forall_const]
    omega
  · intro n hn
    fin_cases hn
    · exact hf1
    · exact hfq
    · exact hm
    · exact hfpq
    · exact hfp2

/-- **Pentad criterion, nonresidue-count form.** Under the tetrad hypotheses
with `p ≡ 3 (mod 4)`: if the number of quadratic nonresidues in
`[1, (p-1)/2]` is even, the pentad `1, q, (p-1)/2, p - 1 - q, p - 2` is
pairwise distinct with all factorials `≡ 1 (mod p)`. -/
theorem pentad_of_even (p q : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3)
    (hq6 : q % 6 = 1) (hq7 : 7 ≤ q) (hdvd : p ∣ q.factorial - 1)
    (hN : Even ((Icc 1 ((p - 1) / 2)).filter
      fun a : ℕ => ¬IsSquare ((a : ZMod p))).card) :
    List.Pairwise (· ≠ ·) [1, q, (p - 1) / 2, p - 1 - q, p - 2] ∧
      ∀ n ∈ [1, q, (p - 1) / 2, p - 1 - q, p - 2], ((n ! : ℕ) : ZMod p) = 1 :=
  pentad_of_dvd p q hq6 hq7 hdvd (by rw [central_sign hp4, hN.neg_one_pow])

end Erdos1056
