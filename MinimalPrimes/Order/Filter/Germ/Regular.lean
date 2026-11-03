/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Order.Filter.Germ.Basic
public import MinimalPrimes.Order.Filter.Product.Regular

/-!
# Regular elements of filter germs

A function represents a left-regular, right-regular, or regular germ precisely when
its values have the corresponding property eventually. The codomain needs only a
multiplication; the filter may be improper and the index or codomain may be empty.

These are the constant-family specializations of the dependent reduced-product
criteria in `MinimalPrimes.Order.Filter.Product.Regular`. The carrier, coercion and
multiplication agree with the existing germ construction.

## References

The dependent argument and its Mathlib references are documented in
`MinimalPrimes.Order.Filter.Product.Regular`.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v} [Mul M]

/-- Left multiplication by a germ is injective exactly when left multiplication by
its representative is injective eventually. -/
theorem isLeftRegular_coe_iff (D : Filter ι) (f : ι → M) :
    IsLeftRegular (f : Germ D M) ↔ ∀ᶠ i in D, IsLeftRegular (f i) :=
  Product.isLeftRegular_coe_iff (K := fun _ : ι => M) D f

/-- Right multiplication by a germ is injective exactly when right multiplication
by its representative is injective eventually. -/
theorem isRightRegular_coe_iff (D : Filter ι) (f : ι → M) :
    IsRightRegular (f : Germ D M) ↔ ∀ᶠ i in D, IsRightRegular (f i) :=
  Product.isRightRegular_coe_iff (K := fun _ : ι => M) D f

/-- A germ is regular exactly when its representative is regular eventually. -/
theorem isRegular_coe_iff (D : Filter ι) (f : ι → M) :
    IsRegular (f : Germ D M) ↔ ∀ᶠ i in D, IsRegular (f i) :=
  Product.isRegular_coe_iff (K := fun _ : ι => M) D f

-- A varying family with NAND multiplication is regular at the principal true
-- coordinate. NAND is nonassociative, so this use needs no semigroup structure.
example [Mul Bool] (hmul : ∀ a b : Bool, a * b = !(a && b)) :
    IsRegular ((fun b : Bool => b) : Germ (Filter.principal {true}) Bool) := by
  apply (isRegular_coe_iff _ _).2
  rw [Filter.eventually_principal]
  intro b hb
  have hb' : b = true := hb
  subst b
  constructor <;> intro x y hxy <;> simp only [hmul] at hxy <;>
    cases x <;> cases y <;> cases hxy <;> rfl

end Filter.Germ
