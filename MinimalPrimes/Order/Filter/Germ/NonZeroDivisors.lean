/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Non-zero-divisors of filter germs

A function represents a left, right, or two-sided non-zero-divisor precisely when
its values have the corresponding property eventually. The codomain is an arbitrary
monoid with zero, and the filter need not be proper.

For necessity, choose a nonzero annihilator wherever the coordinate fails the
criterion, and zero elsewhere. The resulting germ is an annihilator, so it vanishes;
its eventual vanishing forces the coordinate criterion. Sufficiency tests arbitrary
representatives on the intersection of two eventual sets.

## References

The representation and multiplication APIs are Mathlib's `Mathlib.Order.Filter.Germ.Basic`,
formalized by Yury Kudryashov and Abhimanyu Pallavi Sudhir. The non-zero-divisor
submonoids and witness criteria are from `Mathlib.Algebra.GroupWithZero.NonZeroDivisors`,
by Kenny Lau, Devon Tuma and Oliver Nash; witness selection uses `Filter.skolem` from
Mathlib's filter API. The bad-coordinate argument parallels the regularity criteria
in `MinimalPrimes.Order.Filter.Germ.Regular`.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v} {D : Filter ι}

private theorem coe_eq_zero_iff [Zero M] {f : ι → M} :
    (f : Germ D M) = 0 ↔ ∀ᶠ i in D, f i = 0 := by
  simp only [← coe_zero, coe_eq, Filter.EventuallyEq, Pi.zero_apply]

variable [MonoidWithZero M]

/-- A germ is a left non-zero-divisor exactly when its representative is a left
non-zero-divisor eventually. Here left means that `f i * x = 0` forces `x = 0`. -/
theorem mem_nonZeroDivisorsLeft_coe_iff (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ nonZeroDivisorsLeft (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroDivisorsLeft M := by
  classical
  rw [mem_nonZeroDivisorsLeft_iff (Germ D M)]
  constructor
  · intro hf
    have hw : ∀ᶠ i in D, ∃ x : M,
        f i * x = 0 ∧ (x = 0 → f i ∈ nonZeroDivisorsLeft M) := by
      apply Eventually.of_forall
      intro i
      by_cases hi : f i ∈ nonZeroDivisorsLeft M
      · exact ⟨0, mul_zero _, fun _ => hi⟩
      · obtain ⟨x, hx, hne⟩ := (notMem_nonZeroDivisorsLeft_iff M).mp hi
        exact ⟨x, hx, fun h => (hne h).elim⟩
    obtain ⟨g, hg⟩ := Filter.skolem.mp hw
    have hmul : (f : Germ D M) * (g : Germ D M) = 0 := by
      rw [← coe_mul, coe_eq_zero_iff]
      exact hg.mono fun _ hi => hi.1
    have hzero : ∀ᶠ i in D, g i = 0 := coe_eq_zero_iff.mp (hf (g : Germ D M) hmul)
    exact (hg.and hzero).mono fun _ hi => hi.1.2 hi.2
  · intro hf g
    refine inductionOn g ?_
    intro g hmul
    have hz : ∀ᶠ i in D, f i * g i = 0 := by
      rw [← coe_mul, coe_eq_zero_iff] at hmul
      exact hmul
    exact coe_eq_zero_iff.mpr <|
      (hf.and hz).mono fun _ hi => (mem_nonZeroDivisorsLeft_iff M).mp hi.1 _ hi.2

/-- A germ is a right non-zero-divisor exactly when its representative is a right
non-zero-divisor eventually. Here right means that `x * f i = 0` forces `x = 0`. -/
theorem mem_nonZeroDivisorsRight_coe_iff (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ nonZeroDivisorsRight (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroDivisorsRight M := by
  classical
  rw [mem_nonZeroDivisorsRight_iff (Germ D M)]
  constructor
  · intro hf
    have hw : ∀ᶠ i in D, ∃ x : M,
        x * f i = 0 ∧ (x = 0 → f i ∈ nonZeroDivisorsRight M) := by
      apply Eventually.of_forall
      intro i
      by_cases hi : f i ∈ nonZeroDivisorsRight M
      · exact ⟨0, zero_mul _, fun _ => hi⟩
      · obtain ⟨x, hx, hne⟩ := (notMem_nonZeroDivisorsRight_iff M).mp hi
        exact ⟨x, hx, fun h => (hne h).elim⟩
    obtain ⟨g, hg⟩ := Filter.skolem.mp hw
    have hmul : (g : Germ D M) * (f : Germ D M) = 0 := by
      rw [← coe_mul, coe_eq_zero_iff]
      exact hg.mono fun _ hi => hi.1
    have hzero : ∀ᶠ i in D, g i = 0 := coe_eq_zero_iff.mp (hf (g : Germ D M) hmul)
    exact (hg.and hzero).mono fun _ hi => hi.1.2 hi.2
  · intro hf g
    refine inductionOn g ?_
    intro g hmul
    have hz : ∀ᶠ i in D, g i * f i = 0 := by
      rw [← coe_mul, coe_eq_zero_iff] at hmul
      exact hmul
    exact coe_eq_zero_iff.mpr <|
      (hf.and hz).mono fun _ hi => (mem_nonZeroDivisorsRight_iff M).mp hi.1 _ hi.2

/-- A germ is a non-zero-divisor on both sides exactly when its representative is
one eventually. No commutativity or properness assumption is needed. -/
@[simp]
theorem mem_nonZeroDivisors_coe_iff (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ nonZeroDivisors (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroDivisors M := by
  simp only [mem_nonZeroDivisors_iff', mem_nonZeroDivisorsLeft_coe_iff,
    mem_nonZeroDivisorsRight_coe_iff, eventually_and]

end Filter.Germ
