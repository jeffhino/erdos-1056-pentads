/-
Copyright (c) 2026 Jeff Hinojosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeff Hinojosa
-/
import Mathlib.Tactic.NormNum.Prime
import Erdos1056.Tetrad

/-!
# The flagship instance: `p = 5039`

`5039 = 7! - 1` is a prime `≡ 3 (mod 4)`. Modulo `5039` the five pairwise
distinct arguments `1, 7, 2519, 5031, 5037` all have factorial `≡ 1`, where
`2519 = (5039 - 1) / 2` is the central argument, `5031 = 5039 - 1 - 7`, and
`5037 = 5039 - 2`. This realizes the pentad `{1, q, (p-1)/2, p-1-q, p-2}`
at `q = 7`.
-/

namespace Erdos1056

open Nat

theorem prime_5039 : Nat.Prime 5039 := by norm_num

instance : Fact (Nat.Prime 5039) := ⟨prime_5039⟩

theorem mod_four_5039 : 5039 % 4 = 3 := by norm_num

/-- `5039` divides `7! - 1` (indeed equals it). -/
theorem dvd_factorial_seven_sub_one : 5039 ∣ Nat.factorial 7 - 1 := by
  norm_num [Nat.factorial]

/-- The central congruence `2519! ≡ 1 (mod 5039)`, verified by kernel
computation (`2519 = (5039 - 1) / 2`). -/
theorem central_factorial_5039 : ((2519! : ℕ) : ZMod 5039) = 1 := by
  have h : 2519! % 5039 = 1 := by
    set_option maxRecDepth 100000 in decide
  calc ((2519! : ℕ) : ZMod 5039)
      = ((2519! % 5039 : ℕ) : ZMod 5039) := (ZMod.natCast_mod _ _).symm
    _ = 1 := by rw [h]; norm_num

/-- **The flagship pentad.** The five arguments `1, 7, 2519, 5031, 5037` are
pairwise distinct and all have factorial `≡ 1 (mod 5039)`. -/
theorem flagship_pentad :
    List.Pairwise (· ≠ ·) [1, 7, 2519, 5031, 5037] ∧
      ∀ n ∈ [1, 7, 2519, 5031, 5037], ((n ! : ℕ) : ZMod 5039) = 1 := by
  obtain ⟨-, -, h1, h7, h5031, h5037⟩ :=
    tetrad_of_dvd 5039 7 (by norm_num) (by norm_num) dvd_factorial_seven_sub_one
  refine ⟨by decide, ?_⟩
  intro n hn
  fin_cases hn
  · exact h1
  · exact h7
  · exact central_factorial_5039
  · exact h5031
  · exact h5037

end Erdos1056
