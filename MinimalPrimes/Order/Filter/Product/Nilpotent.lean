/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product
public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotence and finite members of filters

If a filter contains a finite set, eventual nilpotence of a dependent section of
monoids with zero has a uniform exponent. Only the indices in that finite member
need a common bound; the whole index type may be infinite. The filter need not
be proper, and the fibres may be trivial.

## References

The bound uses Mathlib's `Set.Finite.exists_le`, `nilpotencyClass`,
`pow_nilpotencyClass` and `pow_eq_zero_of_le`.
-/

@[expose] public section

universe u v

namespace Filter

variable {ι : Type u} {D : Filter ι} {R : ι → Type v}
variable [∀ i, MonoidWithZero (R i)]

/-- Eventual nilpotence has a uniform exponent when the filter contains a finite set.
The exponent may be zero, so trivial fibres and the bottom filter are included. -/
theorem Eventually.exists_pow_eq_zero_of_finite_mem {f : ∀ i, R i}
    (hf : ∀ᶠ i in D, IsNilpotent (f i)) {s : Set ι} (hs : s.Finite) (hsD : s ∈ D) :
    ∃ n : ℕ, ∀ᶠ i in D, f i ^ n = 0 := by
  obtain ⟨n, hn⟩ := (hs.image (fun i => nilpotencyClass (f i))).exists_le
  have hmem : ∀ᶠ i in D, i ∈ s := hsD
  refine ⟨n, (hmem.and hf).mono fun i hi => ?_⟩
  exact pow_eq_zero_of_le (hn _ ⟨i, hi.1, rfl⟩) (pow_nilpotencyClass hi.2)

end Filter
