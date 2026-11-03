/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Germ.NonZeroDivisors
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Cancellation of successor-weighted integer-pair germs

The nonconstant weights `n + 1` reflect zero on integer pairs at every coordinate.
The scalar non-zero-divisor bridge therefore gives cancellation on asymptotic germs,
without claiming a no-zero-divisors property for two varying scalar germs.
-/

@[expose] public section

open Filter

namespace MinimalPrimesTest.GermSMul

/-- Successor weights cancel on germs of integer pairs at infinity. -/
theorem successor_weight_smul_cancel (x y : Germ (atTop : Filter ℕ) (ℤ × ℤ))
    (h : (Germ.ofFun (fun n : ℕ => (n : ℤ) + 1) : Germ (atTop : Filter ℕ) ℤ) • x =
      (Germ.ofFun (fun n : ℕ => (n : ℤ) + 1) : Germ (atTop : Filter ℕ) ℤ) • y) : x = y := by
  have hmem : (Germ.ofFun (fun n : ℕ => (n : ℤ) + 1) : Germ (atTop : Filter ℕ) ℤ) ∈
      nonZeroSMulDivisors (Germ (atTop : Filter ℕ) ℤ)
        (Germ (atTop : Filter ℕ) (ℤ × ℤ)) := by
    apply Germ.mem_nonZeroSMulDivisors_coe_of_eventually
    apply Eventually.of_forall
    intro n
    apply mem_nonZeroSMulDivisors_iff.mpr
    rintro ⟨a, b⟩ hab
    have hn : (n : ℤ) + 1 ≠ 0 :=
      ne_of_gt (add_pos_of_nonneg_of_pos (Int.natCast_nonneg n) zero_lt_one)
    have ha : ((n : ℤ) + 1) * a = 0 := congrArg Prod.fst hab
    have hb : ((n : ℤ) + 1) * b = 0 := congrArg Prod.snd hab
    exact Prod.ext ((mul_eq_zero.mp ha).resolve_left hn) ((mul_eq_zero.mp hb).resolve_left hn)
  apply sub_eq_zero.mp
  apply (mem_nonZeroSMulDivisors_iff.mp hmem) (x - y)
  rw [smul_sub, h, sub_self]

end MinimalPrimesTest.GermSMul
