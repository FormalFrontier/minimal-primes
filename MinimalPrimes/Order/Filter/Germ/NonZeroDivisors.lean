/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import MinimalPrimes.Order.Filter.Germ.SMul

/-!
# Non-zero-divisors of filter germs

A function represents a left, right, or two-sided non-zero-divisor precisely when
its values have the corresponding property eventually. The codomain is an arbitrary
monoid with zero, and the filter need not be proper.

The left and right criteria specialize the pointed-fibre criterion in
`MinimalPrimes.Order.Filter.Germ.Map`, consolidating their annihilator witnesses there.
The scalar criterion retains the stock `MulAction` hypotheses; its converse assumes
only eventual preservation of zero by that selected action.

## References

The representation and multiplication APIs are Mathlib's `Mathlib.Order.Filter.Germ.Basic`,
formalized by Yury Kudryashov and Abhimanyu Pallavi Sudhir. The non-zero-divisor
submonoids and witness criteria are from `Mathlib.Algebra.GroupWithZero.NonZeroDivisors`,
by Kenny Lau, Devon Tuma and Oliver Nash; witness selection uses `Filter.skolem` from
Mathlib's filter API. The bad-coordinate argument parallels the regularity criteria
in `MinimalPrimes.Order.Filter.Germ.Regular`.
-/

@[expose] public section

universe u v w

namespace Filter.Germ

variable {ι : Type u} {M : Type v} {D : Filter ι}

variable {R : Type w}

/-- Eventual scalar zero-reflection implies membership in the stock germ submonoid.
No zero-preservation law is needed in this direction. -/
theorem mem_nonZeroSMulDivisors_coe_of_eventually [MonoidWithZero R] [Zero M]
    [MulAction R M] (D : Filter ι) (f : ι → R)
    (h : ∀ᶠ i in D, f i ∈ nonZeroSMulDivisors R M) :
    (f : Germ D R) ∈ nonZeroSMulDivisors (Germ D R) (Germ D M) := by
  apply mem_nonZeroSMulDivisors_iff.mpr
  apply forall_smul_coe_eq_zero_imp_of_eventually D f
  exact h.mono fun _ hi => mem_nonZeroSMulDivisors_iff.mp hi

/-- Under eventual zero preservation by the selected `MulAction`, a represented scalar
belongs to the stock germ submonoid exactly when it does so eventually in coordinates. -/
theorem mem_nonZeroSMulDivisors_coe_iff [MonoidWithZero R] [Zero M] [MulAction R M]
    (D : Filter ι) (f : ι → R) (h₀ : ∀ᶠ i in D, f i • (0 : M) = 0) :
    (f : Germ D R) ∈ nonZeroSMulDivisors (Germ D R) (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroSMulDivisors R M := by
  simp only [mem_nonZeroSMulDivisors_iff]
  exact forall_smul_coe_eq_zero_imp_iff_of_eventually_smul_zero D f h₀

variable [MonoidWithZero M]

/-- A germ is a left non-zero-divisor exactly when its representative is a left
non-zero-divisor eventually. Here left means that `f i * x = 0` forces `x = 0`. -/
theorem mem_nonZeroDivisorsLeft_coe_iff (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ nonZeroDivisorsLeft (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroDivisorsLeft M := by
  have heval (x : Germ D M) :
      map₂ (fun (φ : M → M) (m : M) => φ m)
        ((fun (i : ι) (m : M) => f i * m) : Germ D (M → M)) x =
          (f : Germ D M) * x := by
    simpa only [map_coe, Function.comp_def, map₂_mul] using
      map₂_apply_map D (fun (a b : M) => a * b) (f : Germ D M) x
  simpa only [mem_nonZeroDivisorsLeft_iff, heval, const_zero] using
    forall_map₂_apply_eq_const_imp_iff D (fun i m => f i * m) (0 : M) (0 : M)
      (Eventually.of_forall fun i => mul_zero (f i))

/-- A germ is a right non-zero-divisor exactly when its representative is a right
non-zero-divisor eventually. Here right means that `x * f i = 0` forces `x = 0`. -/
theorem mem_nonZeroDivisorsRight_coe_iff (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ nonZeroDivisorsRight (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroDivisorsRight M := by
  have heval (x : Germ D M) :
      map₂ (fun (φ : M → M) (m : M) => φ m)
        ((fun (i : ι) (m : M) => m * f i) : Germ D (M → M)) x =
          x * (f : Germ D M) := by
    refine inductionOn x ?_
    intro g
    rw [map₂_coe, ← coe_mul]
    rfl
  simpa only [mem_nonZeroDivisorsRight_iff, heval, const_zero] using
    forall_map₂_apply_eq_const_imp_iff D (fun i m => m * f i) (0 : M) (0 : M)
      (Eventually.of_forall fun i => zero_mul (f i))

/-- A germ is a non-zero-divisor on both sides exactly when its representative is
one eventually. No commutativity or properness assumption is needed. -/
@[simp]
theorem mem_nonZeroDivisors_coe_iff (D : Filter ι) (f : ι → M) :
    (f : Germ D M) ∈ nonZeroDivisors (Germ D M) ↔
      ∀ᶠ i in D, f i ∈ nonZeroDivisors M := by
  simp only [mem_nonZeroDivisors_iff', mem_nonZeroDivisorsLeft_coe_iff,
    mem_nonZeroDivisorsRight_coe_iff, eventually_and]

end Filter.Germ
