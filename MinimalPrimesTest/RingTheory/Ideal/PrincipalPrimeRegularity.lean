/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight
import Mathlib.Algebra.Divisibility.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# A prime zero-divisor generating an ideal of height zero

The element `2` in `ZMod 4` is prime but is not a non-zero-divisor: its square is zero.
Strict divisibility is well-founded in this ring. A rank assigning zero to units, one to
`2`, and two to zero increases along `DvdNotUnit`; this is a calculation in four elements,
not an application of a domain instance.

The nonzero, proper principal prime ideal `(2)` has height zero by Mathlib's Artinian
minimal-prime API. The principal-prime upper bound from MinimalPrimes still applies, but
the height-one conclusion fails. Thus regularity cannot be omitted from the
regular-generator equality, even when strict divisibility is well-founded.

## References

These examples use the upper bound in
`MinimalPrimes.RingTheory.Ideal.PrincipalPrimeHeight`. The finite calculations use
Mathlib's `ZMod.isUnit_iff_coprime`, finite divisibility and inverse-image well-foundedness
through `measure`. The height calculation reuses Mathlib's `isArtinian_of_finite`,
`IsArtinianRing.mem_minimalPrimes`, and `Ideal.height_eq_zero_iff`.
-/

namespace PrincipalPrimeRegularityExamples

private theorem two_prime : Prime (2 : ZMod 4) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [← Nat.cast_two, ZMod.isUnit_iff_coprime 2 4, Nat.coprime_iff_gcd_eq_one]
    decide
  · decide

private theorem two_not_mem_nonZeroDivisors :
    (2 : ZMod 4) ∉ nonZeroDivisors (ZMod 4) :=
  notMem_nonZeroDivisors_iff_right.mpr ⟨2, by decide, by decide⟩

private theorem two_not_isRegular : ¬ IsRegular (2 : ZMod 4) :=
  fun h => two_not_mem_nonZeroDivisors h.mem_nonZeroDivisors

private def divisibilityRank (a : ZMod 4) : ℕ :=
  if a = 0 then 2 else if a = 2 then 1 else 0

private theorem divisibilityRank_lt_of_dvdNotUnit {a b : ZMod 4} (h : DvdNotUnit a b) :
    divisibilityRank a < divisibilityRank b := by
  rcases h with ⟨ha, x, hx, rfl⟩
  have hx' : ¬ x.val.Coprime 4 := by
    intro hcoprime
    apply hx
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime x.val 4).mpr hcoprime
  rw [Nat.coprime_iff_gcd_eq_one] at hx'
  have hlt : ∀ u v : ZMod 4, u ≠ 0 → ¬ v.val.gcd 4 = 1 →
      divisibilityRank u < divisibilityRank (u * v) := by decide
  exact hlt a x ha hx'

private theorem zmod_four_wfDvdMonoid : WfDvdMonoid (ZMod 4) := by
  refine ⟨(measure divisibilityRank).wf.mono ?_⟩
  intro a b h
  exact divisibilityRank_lt_of_dvdNotUnit h

private theorem span_two_isPrime : (Ideal.span {(2 : ZMod 4)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime two_prime

private theorem span_two_ne_top : (Ideal.span {(2 : ZMod 4)}) ≠ ⊤ :=
  span_two_isPrime.ne_top

private theorem span_two_ne_bot : (Ideal.span {(2 : ZMod 4)}) ≠ ⊥ :=
  fun h => two_prime.ne_zero (Ideal.span_singleton_eq_bot.mp h)

private theorem height_span_two_eq_zero : (Ideal.span {(2 : ZMod 4)}).height = 0 := by
  let : IsArtinianRing (ZMod 4) := isArtinian_of_finite
  let : (Ideal.span {(2 : ZMod 4)}).IsPrime := span_two_isPrime
  exact Ideal.height_eq_zero_iff.mpr (IsArtinianRing.mem_minimalPrimes bot_le)

private theorem height_span_two_ne_one : (Ideal.span {(2 : ZMod 4)}).height ≠ 1 := by
  rw [height_span_two_eq_zero]
  exact zero_ne_one

private theorem height_span_two_le_one : (Ideal.span {(2 : ZMod 4)}).height ≤ 1 := by
  let : WfDvdMonoid (ZMod 4) := zmod_four_wfDvdMonoid
  exact Ideal.height_span_singleton_le_one_of_prime two_prime

end PrincipalPrimeRegularityExamples
