/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Germ.Map
public import Mathlib.Order.Filter.Cofinite

/-!
# Eventual cancellation with an exceptional fibre

The varying family is the constant-zero map at index zero and addition by `n` at
each positive index `n`. Its action on sequence germs at the cofinite filter is
injective, even though its zero fibre is not injective.
-/

@[expose] public section

open Filter

namespace MinimalPrimesTest.GermMap

/-- The exceptional zero fibre is constant; positive fibres translate by their index. -/
def exceptionalShift (n k : ℕ) : ℕ := if n = 0 then 0 else n + k

/-- Eventual injectivity gives cancellation on germs despite the bad zero fibre. -/
theorem exceptionalShift_germ_injective_but_not_zero :
    Function.Injective
      (Germ.map₂ (fun (φ : ℕ → ℕ) (a : ℕ) => φ a)
        (exceptionalShift : Germ (cofinite : Filter ℕ) (ℕ → ℕ))) ∧
      ¬Function.Injective (exceptionalShift 0) := by
  constructor
  · apply (Germ.injective_map₂_apply_coe_iff cofinite exceptionalShift).mpr
    filter_upwards [eventually_cofinite_ne (0 : ℕ)] with n hn
    intro a b hab
    exact Nat.add_left_cancel (by simpa only [exceptionalShift, ite_eq_right hn] using hab)
  · intro h
    have heq : (0 : ℕ) = 1 := h (by simp [exceptionalShift])
    exact Nat.zero_ne_one heq

end MinimalPrimesTest.GermMap
