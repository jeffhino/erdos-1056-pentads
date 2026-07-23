/-
Copyright (c) 2026 Jeff Hinojosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeff Hinojosa
-/
import Mathlib.NumberTheory.Wilson

/-!
# Wilson pairing

For a prime `p` and `0 ≤ n ≤ p - 1`, we have
`n! * (p - 1 - n)! ≡ (-1) ^ (n + 1) (mod p)`.

This generalizes Wilson's theorem (the case `n = 0`), and is proved by
induction on `n`: each step trades the factor `p - 1 - n ≡ -(n + 1) (mod p)`
of the right factorial for the factor `n + 1` of the left one, at the cost
of a sign.
-/

namespace Erdos1056

open Nat

/-- **Wilson pairing.** For a prime `p` and `n ≤ p - 1`,
`n! * (p - 1 - n)! ≡ (-1) ^ (n + 1) (mod p)`. -/
theorem wilson_pairing (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : n ≤ p - 1) :
    (n ! : ZMod p) * ((p - 1 - n)! : ZMod p) = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [ZMod.wilsons_lemma p]
  | succ k ih =>
    have hp2 : 2 ≤ p := hp.out.two_le
    have hk : k ≤ p - 1 := Nat.le_of_succ_le hn
    have ih' := ih hk
    -- split off the top factor of `(p - 1 - k)!`
    have hsplit : p - 1 - k = (p - 1 - (k + 1)) + 1 := by omega
    have hfac : (p - 1 - k)! = (p - 1 - k) * (p - 1 - (k + 1))! := by
      rw [hsplit, Nat.factorial_succ]
    -- `p - 1 - k ≡ -(k + 1) (mod p)`
    have hcast : ((p - 1 - k : ℕ) : ZMod p) = -((k + 1 : ℕ) : ZMod p) := by
      have h : (p - 1 - k) + (k + 1) = p := by omega
      have h2 : (((p - 1 - k) + (k + 1) : ℕ) : ZMod p) = 0 := by
        rw [h]; exact ZMod.natCast_self p
      rw [Nat.cast_add] at h2
      exact eq_neg_of_add_eq_zero_left h2
    rw [hfac, Nat.cast_mul, hcast] at ih'
    rw [Nat.factorial_succ]
    push_cast at ih' ⊢
    linear_combination (-1 : ZMod p) * ih'

end Erdos1056
