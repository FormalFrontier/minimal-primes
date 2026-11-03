/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Units in dependent reduced products

A represented element of a dependent filter product is a unit exactly when its
section is a unit on a filter-large set. The coefficient monoids need not be
commutative, and the filter need not be proper. Every unit of the reduced product
has an everywhere-unit section representative.

## Implementation notes

The forward implication uses both inverse identities on a common filter-large set.
For the converse, replacing nonunit values by `1` gives a unit in the total section
monoid, whose image under `Filter.Product.coeMulHom` is the original class.
The representative-surjectivity theorem uses `Filter.skolem` and
`MulEquiv.piUnits`, without constructing another equivalence of units.
The constant-family specializations are retained in
`MinimalPrimes.Order.Filter.Germ.Units`.

## References

The unit-locus argument generalizes the germ formalization by Formal Frontier Agents.
The carrier and eventual-equality API use Mathlib's germ formalization by Yury
Kudryashov and Abhimanyu Pallavi Sudhir. The total-section unit criterion and unit
equivalence are Andrew Yang's `Pi.isUnit_iff` and `MulEquiv.piUnits`.
The units homomorphism API was formalized by Johan Commelin, Chris Hughes and Kevin
Buzzard. Representative choice uses the filter API developed by Johannes Hölzl and
Jeremy Avigad.
-/

@[expose] public section

universe u v

namespace Filter.Product

variable {ι : Type u} {K : ι → Type v} [∀ i, Monoid (K i)]

/-- A dependent reduced-product class is a unit if and only if its section is eventually
    a unit. This generalizes the unit-locus argument for germs. -/
@[simp]
theorem isUnit_coe_iff (F : Filter ι) (f : ∀ i, K i) :
    @IsUnit (F.Product K) inferInstance (f : F.Product K) ↔
      ∀ᶠ i in F, IsUnit (f i) := by
  constructor
  · intro hf
    obtain ⟨g, hfg, hgf⟩ := isUnit_iff_exists.mp hf
    revert hfg hgf
    refine Quotient.inductionOn g fun g hfg hgf => ?_
    have hfg' : ∀ᶠ i in F, f i * g i = 1 := (coe_eq (f * g) 1).mp hfg
    have hgf' : ∀ᶠ i in F, g i * f i = 1 := (coe_eq (g * f) 1).mp hgf
    filter_upwards [hfg', hgf'] with i hfg hgf
    exact isUnit_iff_exists.mpr ⟨g i, hfg, hgf⟩
  · intro hf
    classical
    let g : ∀ i, K i := fun i => if IsUnit (f i) then f i else 1
    have hg : IsUnit g := Pi.isUnit_iff.mpr fun i => by
      by_cases hi : IsUnit (f i) <;> simp [g, hi]
    have hgf : (g : F.Product K) = (f : F.Product K) :=
      (coe_eq g f).mpr <| hf.mono fun i hi => by simp [g, hi]
    exact hgf ▸ IsUnit.map (coeMulHom F) hg

/-- Every unit of a dependent reduced product has a representative that is a unit in
    the total section monoid, using the stock total-product unit equivalence. -/
theorem units_map_coeMulHom_surjective (F : Filter ι) :
    Function.Surjective (Units.map (coeMulHom F : (∀ i, K i) →* F.Product K)) := by
  intro u
  obtain ⟨f, hf⟩ : ∃ f : (∀ i, K i), (f : F.Product K) = (u : F.Product K) :=
    Quotient.mk_surjective (u : F.Product K)
  have hf' : ∀ᶠ i in F, ∃ v : (K i)ˣ, (v : K i) = f i :=
    (isUnit_coe_iff F f).mp (by simpa only [hf] using u.isUnit)
  obtain ⟨v, hv⟩ : ∃ v : ∀ i, (K i)ˣ, ∀ᶠ i in F, (v i : K i) = f i :=
    Filter.skolem.mp hf'
  refine ⟨MulEquiv.piUnits.symm v, Units.ext ?_⟩
  exact ((coe_eq (fun i => (v i : K i)) f).mpr hv).trans hf

end Filter.Product
