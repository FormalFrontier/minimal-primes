/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Units in monoids of filter germs

A germ is a unit exactly when its representative is a unit on a filter-large set.
The coefficient monoid need not be commutative, and the filter need not be proper.

## Implementation notes

The forward implication uses both inverse identities on a common filter-large set.
For the converse, replacing nonunit values by `1` gives a unit in the total function
monoid, whose image under `Filter.Germ.coeMulHom` is the original germ.

## References

The proof uses Mathlib's germ quotient and coercion monoid homomorphism, formalized
by Yury Kudryashov and Abhimanyu Pallavi Sudhir, and Andrew Yang's total-product
unit criterion `Pi.isUnit_iff`.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v} [Monoid M]

/-- A germ in a monoid is a unit if and only if its representative is eventually a unit. -/
theorem isUnit_coe_iff (D : Filter ι) (f : ι → M) :
    IsUnit (f : Filter.Germ D M) ↔ ∀ᶠ i in D, IsUnit (f i) := by
  constructor
  · intro hf
    obtain ⟨g, hfg, hgf⟩ := isUnit_iff_exists.mp hf
    revert hfg hgf
    refine inductionOn g fun g hfg hgf => ?_
    have hfg' : ∀ᶠ i in D, f i * g i = 1 := coe_eq.mp hfg
    have hgf' : ∀ᶠ i in D, g i * f i = 1 := coe_eq.mp hgf
    filter_upwards [hfg', hgf'] with i hfg hgf
    exact isUnit_iff_exists.mpr ⟨g i, hfg, hgf⟩
  · intro hf
    classical
    let g : ι → M := fun i => if IsUnit (f i) then f i else 1
    have hg : IsUnit g := Pi.isUnit_iff.mpr fun i => by
      by_cases hi : IsUnit (f i) <;> simp [g, hi]
    have hgf : (g : Filter.Germ D M) = f :=
      coe_eq.mpr <| hf.mono fun i hi => by simp [g, hi]
    exact hgf ▸ IsUnit.map (coeMulHom D) hg

end Filter.Germ
