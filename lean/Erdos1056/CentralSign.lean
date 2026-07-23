/-
Copyright (c) 2026 Jeff Hinojosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeff Hinojosa
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Erdos1056.WilsonPairing

/-!
# The central sign

For a prime `p ≡ 3 (mod 4)` with `m = (p - 1) / 2`, we prove
`m! ≡ (-1) ^ N (mod p)`, where `N` is the number of quadratic nonresidues
in `[1, m]`.

The proof avoids the class number formula entirely. Because `-1` is a
nonresidue when `p ≡ 3 (mod 4)`, the map sending `a ∈ [1, m]` to `a` if `a`
is a residue and to `-a` otherwise is an injection onto the set of nonzero
quadratic residues, as is the map `b ↦ b²`. Comparing the two products gives
`(-1)^N · m! = (m!)²`, and `(m!)² ≡ 1` by the Wilson pairing at the center
(`m` is odd here), so `m! ≡ (-1)^N`.
-/

namespace Erdos1056

open Nat Finset

/-- `∏_{a=1}^{n} a = n!` as a product over `Finset.Icc`. -/
theorem prod_Icc_one_id (n : ℕ) : (∏ a ∈ Icc 1 n, a) = n ! := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]

section CastLemmas

variable {p : ℕ}

/-- Distinct residues below `p` have distinct casts. -/
theorem cast_inj_of_lt {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = b) : a = b := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hv

/-- A number in `[1, p)` has nonzero cast. -/
theorem cast_ne_zero_of_lt {a : ℕ} (h1 : 1 ≤ a) (h2 : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro h
  have hdvd := (ZMod.natCast_eq_zero_iff a p).mp h
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Two numbers in `[1, p)` with sum below `p` are not mirror images. -/
theorem cast_ne_neg {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < p) :
    (a : ZMod p) ≠ -(b : ZMod p) := by
  intro h
  have h0 : ((a + b : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h0
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end CastLemmas

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every nonzero square in `ZMod p` (`p` odd) is the square of the cast of
some `b ∈ [1, (p-1)/2]`. -/
theorem exists_sq_cast_eq (hpodd : p % 2 = 1) {x : ZMod p} (hx : x ≠ 0)
    (hsq : IsSquare x) :
    ∃ b ∈ Icc 1 ((p - 1) / 2), ((b : ℕ) : ZMod p) ^ 2 = x := by
  obtain ⟨y, rfl⟩ := hsq
  have hy : y ≠ 0 := by rintro rfl; simp at hx
  have hvp : y.val < p := ZMod.val_lt y
  have hv0 : y.val ≠ 0 := fun h => hy ((ZMod.val_eq_zero y).mp h)
  by_cases hvm : y.val ≤ (p - 1) / 2
  · refine ⟨y.val, Finset.mem_Icc.mpr ⟨by omega, hvm⟩, ?_⟩
    rw [ZMod.natCast_zmod_val, pow_two]
  · refine ⟨p - y.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hcast : ((p - y.val : ℕ) : ZMod p) = -y := by
      rw [Nat.cast_sub hvp.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
      ring
    rw [hcast, neg_sq, pow_two]

/-- For `p ≡ 3 (mod 4)`, the negative of a nonzero nonsquare is a square. -/
theorem isSquare_neg_of_not_isSquare (hp4 : p % 4 = 3) {x : ZMod p}
    (hx : x ≠ 0) (h : ¬IsSquare x) : IsSquare (-x) := by
  have hns1 : ¬IsSquare (-1 : ZMod p) := fun hs =>
    (ZMod.exists_sq_eq_neg_one_iff.mp hs) hp4
  have h1 : quadraticChar (ZMod p) x = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr h
  have h2 : quadraticChar (ZMod p) (-1 : ZMod p) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hns1
  have h3 : quadraticChar (ZMod p) (-x) = 1 := by
    have hx' : (-x : ZMod p) = (-1) * x := by ring
    rw [hx', map_mul, h2, h1]
    ring
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hx)).mp h3

/-- The signed folding map and the squaring map on `[1, (p-1)/2]` have the
same image in `ZMod p` (both enumerate the nonzero quadratic residues), and
both are injective; hence the products agree. -/
theorem prod_signed_eq_prod_sq (hp4 : p % 4 = 3) :
    (∏ a ∈ Icc 1 ((p - 1) / 2),
        (if IsSquare ((a : ZMod p)) then ((a : ZMod p)) else -((a : ZMod p)))) =
      ∏ a ∈ Icc 1 ((p - 1) / 2), ((a : ZMod p)) ^ 2 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpodd : p % 2 = 1 := by omega
  have h2m : 2 * ((p - 1) / 2) + 1 = p := by omega
  set m := (p - 1) / 2 with hm
  set F : ℕ → ZMod p :=
    fun a => if IsSquare ((a : ZMod p)) then ((a : ZMod p)) else -((a : ZMod p))
    with hF
  set G : ℕ → ZMod p := fun a => ((a : ZMod p)) ^ 2 with hG
  -- bounds
  have hbnd : ∀ a ∈ Icc 1 m, 1 ≤ a ∧ a < p := by
    intro a ha
    have := Finset.mem_Icc.mp ha
    omega
  -- injectivity of the signed map
  have hFinj : ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, F a = F b → a = b := by
    intro a ha b hb hab
    obtain ⟨ha1, hap⟩ := hbnd a ha
    obtain ⟨hb1, hbp⟩ := hbnd b hb
    have habp : a + b < p := by
      have := Finset.mem_Icc.mp ha
      have := Finset.mem_Icc.mp hb
      omega
    rw [hF] at hab
    simp only at hab
    by_cases hA : IsSquare ((a : ZMod p)) <;> by_cases hB : IsSquare ((b : ZMod p))
    · rw [if_pos hA, if_pos hB] at hab
      exact cast_inj_of_lt hap hbp hab
    · rw [if_pos hA, if_neg hB] at hab
      exact absurd hab (cast_ne_neg ha1 hb1 habp)
    · rw [if_neg hA, if_pos hB] at hab
      exact absurd hab.symm (cast_ne_neg hb1 ha1 (by omega))
    · rw [if_neg hA, if_neg hB, neg_inj] at hab
      exact cast_inj_of_lt hap hbp hab
  -- injectivity of the squaring map
  have hGinj : ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, G a = G b → a = b := by
    intro a ha b hb hab
    obtain ⟨ha1, hap⟩ := hbnd a ha
    obtain ⟨hb1, hbp⟩ := hbnd b hb
    have habp : a + b < p := by
      have := Finset.mem_Icc.mp ha
      have := Finset.mem_Icc.mp hb
      omega
    rw [hG] at hab
    simp only at hab
    have hfac : (((a : ZMod p)) - b) * (((a : ZMod p)) + b) = 0 := by
      have h' : ((a : ZMod p)) ^ 2 - ((b : ZMod p)) ^ 2 = 0 := by
        rw [hab]; ring
      calc (((a : ZMod p)) - b) * (((a : ZMod p)) + b)
          = ((a : ZMod p)) ^ 2 - ((b : ZMod p)) ^ 2 := by ring
        _ = 0 := h'
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact cast_inj_of_lt hap hbp (by linear_combination h0)
    · exact absurd (by linear_combination h0 : (a : ZMod p) = -(b : ZMod p))
        (cast_ne_neg ha1 hb1 habp)
  -- the images agree
  have himg : (Icc 1 m).image F = (Icc 1 m).image G := by
    have hsub : (Icc 1 m).image F ⊆ (Icc 1 m).image G := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha1, hap⟩ := hbnd a ha
      have hane : (a : ZMod p) ≠ 0 := cast_ne_zero_of_lt ha1 hap
      rw [hF]
      simp only
      by_cases hA : IsSquare ((a : ZMod p))
      · rw [if_pos hA]
        obtain ⟨b, hb, hbeq⟩ := exists_sq_cast_eq hpodd hane hA
        exact Finset.mem_image.mpr ⟨b, hb, hbeq⟩
      · rw [if_neg hA]
        have hnsq : IsSquare (-(a : ZMod p)) :=
          isSquare_neg_of_not_isSquare hp4 hane hA
        obtain ⟨b, hb, hbeq⟩ :=
          exists_sq_cast_eq hpodd (neg_ne_zero.mpr hane) hnsq
        exact Finset.mem_image.mpr ⟨b, hb, hbeq⟩
    have hcard : ((Icc 1 m).image G).card ≤ ((Icc 1 m).image F).card := by
      rw [Finset.card_image_of_injOn fun a ha b hb => hGinj a ha b hb,
        Finset.card_image_of_injOn fun a ha b hb => hFinj a ha b hb]
    exact Finset.eq_of_subset_of_card_le hsub hcard
  calc ∏ a ∈ Icc 1 m, F a
      = ∏ x ∈ (Icc 1 m).image F, x := by rw [Finset.prod_image hFinj]
    _ = ∏ x ∈ (Icc 1 m).image G, x := by rw [himg]
    _ = ∏ a ∈ Icc 1 m, G a := by rw [Finset.prod_image hGinj]

/-- **The central sign.** For a prime `p ≡ 3 (mod 4)` with `m = (p - 1) / 2`,
`m! ≡ (-1) ^ N (mod p)` where `N` is the number of quadratic nonresidues in
`[1, m]`. -/
theorem central_sign (hp4 : p % 4 = 3) :
    ((((p - 1) / 2)! : ℕ) : ZMod p) =
      (-1) ^ ((Icc 1 ((p - 1) / 2)).filter
          fun a : ℕ => ¬IsSquare ((a : ZMod p))).card := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpodd : p % 2 = 1 := by omega
  have h2m : 2 * ((p - 1) / 2) + 1 = p := by omega
  set m := (p - 1) / 2 with hm
  set N := ((Icc 1 m).filter fun a : ℕ => ¬IsSquare ((a : ZMod p))).card with hN
  have hmodd : m % 2 = 1 := by omega
  -- cast the factorial to a product
  have hfact : ((m ! : ℕ) : ZMod p) = ∏ a ∈ Icc 1 m, ((a : ZMod p)) := by
    rw [← prod_Icc_one_id m, Nat.cast_prod]
  -- the two enumerations of the quadratic residues
  have key := prod_signed_eq_prod_sq (p := p) hp4
  rw [← hm] at key
  -- fold the signs out of the left product
  have hsplit : ∀ a ∈ Icc 1 m,
      (if IsSquare ((a : ZMod p)) then ((a : ZMod p)) else -((a : ZMod p))) =
        (if IsSquare ((a : ZMod p)) then (1 : ZMod p) else -1) * ((a : ZMod p)) := by
    intro a _
    split <;> ring
  rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const, one_pow, one_mul, Finset.prod_pow,
    ← hfact] at key
  -- the square of the central factorial is 1, by Wilson pairing at the center
  have hw := wilson_pairing p (n := m) (by omega)
  have hmm : p - 1 - m = m := by omega
  have heven : Even (m + 1) := Nat.even_iff.mpr (by omega)
  rw [hmm, heven.neg_one_pow] at hw
  rw [pow_two, hw] at key
  -- conclude: (-1)^N * m! = 1 forces m! = (-1)^N
  have hsq : ((-1 : ZMod p) ^ N) * ((-1 : ZMod p) ^ N) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨N, rfl⟩
  calc ((m ! : ℕ) : ZMod p)
      = (((-1 : ZMod p) ^ N) * ((-1 : ZMod p) ^ N)) * ((m ! : ℕ) : ZMod p) := by
        rw [hsq, one_mul]
    _ = ((-1 : ZMod p) ^ N) * (((-1 : ZMod p) ^ N) * ((m ! : ℕ) : ZMod p)) := by
        ring
    _ = ((-1 : ZMod p) ^ N) * 1 := by rw [key]
    _ = (-1 : ZMod p) ^ N := mul_one _

end Prime

end Erdos1056
