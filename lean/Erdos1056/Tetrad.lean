/-
Copyright (c) 2026 Jeff Hinojosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeff Hinojosa
-/
import Erdos1056.WilsonPairing

/-!
# The tetrad theorem

Following Agustín-Aquino and Hernández Santiago: for `q ≡ 1 (mod 6)`, `q ≥ 7`,
the number `q! - 1` has a prime factor `p ≡ 3 (mod 4)`, necessarily `p > q`,
and modulo any such `p` the four distinct arguments `1, q, p - 1 - q, p - 2`
all have factorial `≡ 1 (mod p)`.
-/

namespace Erdos1056

open Nat

/-- Any natural number `≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`. -/
theorem exists_prime_factor_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, pp, pdvd⟩ := Nat.exists_prime_and_dvd hn1
    by_cases hp4 : p % 4 = 3
    · exact ⟨p, pp, hp4, pdvd⟩
    · -- `p` is odd (else `4 ∤ n` fails), so `p ≡ 1 (mod 4)`; recurse into `n / p`
      have hp2 : p ≠ 2 := by
        rintro rfl
        obtain ⟨k, rfl⟩ := pdvd
        omega
      have hodd : p % 2 = 1 := pp.eq_two_or_odd.resolve_left hp2
      have hp1 : p % 4 = 1 := by omega
      obtain ⟨m, rfl⟩ := pdvd
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn
        · exact h
      have hm4 : m % 4 = 3 := by
        have h := Nat.mul_mod p m 4
        rw [hp1] at h
        omega
      have hmlt : m < p * m := by
        have h2 : 2 ≤ p := pp.two_le
        calc m = 1 * m := (one_mul m).symm
        _ < p * m := Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hm0
      obtain ⟨r, rr, hr4, rdvd⟩ := ih m hmlt hm4
      exact ⟨r, rr, hr4, rdvd.mul_left p⟩

/-- For `q ≥ 4`, `q! - 1 ≡ 3 (mod 4)`. -/
theorem factorial_sub_one_mod_four {q : ℕ} (hq : 4 ≤ q) : (q.factorial - 1) % 4 = 3 := by
  have h4 : (4 : ℕ) ∣ q ! := by
    have h24 : (4 : ℕ) ∣ 4 ! := by decide
    exact h24.trans (Nat.factorial_dvd_factorial hq)
  have h1 : 1 ≤ q ! := q.factorial_pos
  omega

/-- A prime factor of `q! - 1` exceeds `q`. -/
theorem lt_of_prime_dvd_factorial_sub_one {p q : ℕ} (pp : p.Prime)
    (h : p ∣ q.factorial - 1) : q < p := by
  by_contra hlt
  have hle : p ≤ q := by omega
  have h1 : p ∣ q ! := Nat.dvd_factorial pp.pos hle
  have h2 : p ∣ q.factorial - (q.factorial - 1) := Nat.dvd_sub h1 h
  have h3 : q.factorial - (q.factorial - 1) = 1 := by have := q.factorial_pos; omega
  rw [h3, Nat.dvd_one] at h2
  exact pp.one_lt.ne' h2

/-- For `q ≡ 1 (mod 6)` with `q ≥ 7`, `q + 2` is composite (it is a multiple
of `3` exceeding `3`). -/
theorem not_prime_q_add_two {q : ℕ} (hq6 : q % 6 = 1) (hq7 : 7 ≤ q) :
    ¬ (q + 2).Prime := by
  intro hp
  have h3 : (3 : ℕ) ∣ q + 2 := by omega
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega

/-- For `q ≡ 1 (mod 6)` with `q ≥ 7`, `2q + 1` is composite (it is a multiple
of `3` exceeding `3`). -/
theorem not_prime_two_mul_add_one {q : ℕ} (hq6 : q % 6 = 1) (hq7 : 7 ≤ q) :
    ¬ (2 * q + 1).Prime := by
  intro hp
  have h3 : (3 : ℕ) ∣ 2 * q + 1 := by omega
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega

/-- `q! ≡ 1 (mod p)` for any `p ∣ q! - 1`. -/
theorem factorial_congr_one {p q : ℕ} (hdvd : p ∣ q.factorial - 1) :
    ((q ! : ℕ) : ZMod p) = 1 := by
  have h1 : q ! = (q.factorial - 1) + 1 := by have := q.factorial_pos; omega
  rw [h1, Nat.cast_add, Nat.cast_one, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, zero_add]

/-- **Tetrad, pointwise form.** If `p` is prime, `q ≡ 1 (mod 6)`, `q ≥ 7`, and
`p ∣ q! - 1`, then `q < p`, the four numbers `1, q, p - 1 - q, p - 2` are
pairwise distinct, and each has factorial `≡ 1 (mod p)`. -/
theorem tetrad_of_dvd (p q : ℕ) [hp : Fact p.Prime] (hq6 : q % 6 = 1)
    (hq7 : 7 ≤ q) (hdvd : p ∣ q.factorial - 1) :
    q < p ∧
      (1 ≠ q ∧ 1 ≠ p - 1 - q ∧ 1 ≠ p - 2 ∧
        q ≠ p - 1 - q ∧ q ≠ p - 2 ∧ p - 1 - q ≠ p - 2) ∧
      ((1! : ZMod p) = 1 ∧ (q ! : ZMod p) = 1 ∧
        ((p - 1 - q)! : ZMod p) = 1 ∧ ((p - 2)! : ZMod p) = 1) := by
  have hqp : q < p := lt_of_prime_dvd_factorial_sub_one hp.out hdvd
  have hp2 : 2 ≤ p := hp.out.two_le
  -- ruled-out coincidences
  have hne1 : p ≠ q + 2 := fun h => not_prime_q_add_two hq6 hq7 (h ▸ hp.out)
  have hne2 : p ≠ 2 * q + 1 := fun h => not_prime_two_mul_add_one hq6 hq7 (h ▸ hp.out)
  refine ⟨hqp, ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · exact factorial_congr_one hdvd
  · -- Wilson pairing at `n = q`, using `q` odd and `q! ≡ 1`
    have hpair := wilson_pairing p (n := q) (by omega)
    have heven : Even (q + 1) := Nat.even_iff.mpr (by omega)
    rw [factorial_congr_one hdvd, one_mul, heven.neg_one_pow] at hpair
    exact hpair
  · -- Wilson pairing at `n = 1`
    have hpair := wilson_pairing p (n := 1) (by omega)
    have h11 : p - 1 - 1 = p - 2 := by omega
    rw [h11] at hpair
    simpa using hpair

/-- **Tetrad, existence form.** For `q ≡ 1 (mod 6)` with `q ≥ 7`, there is a
prime `p ≡ 3 (mod 4)` dividing `q! - 1`; it satisfies `q < p`, and the four
distinct numbers `1, q, p - 1 - q, p - 2` all have factorial `≡ 1 (mod p)`. -/
theorem tetrad (q : ℕ) (hq6 : q % 6 = 1) (hq7 : 7 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ q.factorial - 1 ∧ q < p ∧
      (1 ≠ q ∧ 1 ≠ p - 1 - q ∧ 1 ≠ p - 2 ∧
        q ≠ p - 1 - q ∧ q ≠ p - 2 ∧ p - 1 - q ≠ p - 2) ∧
      ((1! : ZMod p) = 1 ∧ (q ! : ZMod p) = 1 ∧
        ((p - 1 - q)! : ZMod p) = 1 ∧ ((p - 2)! : ZMod p) = 1) := by
  obtain ⟨p, pp, hp4, hdvd⟩ :=
    exists_prime_factor_mod_four_eq_three _
      (factorial_sub_one_mod_four (q := q) (by omega))
  haveI : Fact p.Prime := ⟨pp⟩
  obtain ⟨hqp, hdist, hfacts⟩ := tetrad_of_dvd p q hq6 hq7 hdvd
  exact ⟨p, pp, hp4, hdvd, hqp, hdist, hfacts⟩

end Erdos1056
