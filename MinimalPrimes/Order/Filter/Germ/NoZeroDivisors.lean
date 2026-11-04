/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.NoZeroDivisors

/-!
# No zero divisors in ultrafilter germs

For a value type with only zero and multiplication, its germ at an ultrafilter
has no zero divisors exactly when the value type does. The criterion specializes
the dependent-product theorem to constant fibres, using the existing germ carrier,
zero and multiplication. It needs no associativity, absorption or nontriviality.

The operation comparisons hold for every filter. Only the no-zero-divisor criterion
requires an ultrafilter: at a general proper filter, complementary supports can
represent nonzero factors whose product is zero.

## References

The carrier and operations are Mathlib's filter germs, formalized by Yury Kudryashov
and Abhimanyu Pallavi Sudhir. The criterion reuses the dependent-product theorem in
`MinimalPrimes.Order.Filter.Product.NoZeroDivisors` without a separate quotient or
witness-selection argument.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v}

/-- On constant fibres, congruence multiplication is the existing germ multiplication,
defined by `Germ.map₂`. -/
theorem productCon_hasMul_eq [Mul M] (F : Filter ι) :
    Con.hasMul (productCon F (fun _ : ι => M)) = Germ.instMul (l := F) (M := M) := rfl

/-- On constant fibres, the congruence zero is the existing germ zero. -/
theorem productCon_zero_eq [Zero M] [Mul M] (F : Filter ι) :
    Con.zero (productCon F (fun _ : ι => M)) = Germ.instZero (l := F) (M := M) := rfl

variable [Zero M] [Mul M]

/-- An ultrafilter germ has no zero divisors exactly when its value type has
no zero divisors eventually. The operations need only zero and multiplication. -/
theorem noZeroDivisors_iff_eventually (U : Ultrafilter ι) :
    NoZeroDivisors (Germ (U : Filter ι) M) ↔
      ∀ᶠ _ : ι in (U : Filter ι), NoZeroDivisors M :=
  Product.noZeroDivisors_iff_eventually (R := fun _ : ι => M) U

/-- A germ at an ultrafilter has no zero divisors if and only if its value type does. -/
theorem noZeroDivisors_iff (U : Ultrafilter ι) :
    NoZeroDivisors (Germ (U : Filter ι) M) ↔ NoZeroDivisors M :=
  (noZeroDivisors_iff_eventually U).trans eventually_const

end Filter.Germ
