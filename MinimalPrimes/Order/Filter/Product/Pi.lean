/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.Order.Filter.Finite
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import MinimalPrimes.Order.Filter.Product
public import MinimalPrimes.Order.Filter.Product.Map

/-!
# Dependent reduced products and small products

Coordinate evaluation induces a comparison from the reduced product of a family
of function types to the function type of the coordinate reduced products. This
comparison is surjective for every coordinate index type. It is bijective when
the coordinate type has cardinality less than a cardinal for which the filter is
closed under smaller intersections, giving `Filter.Product.piEquivOfHasCardinalLT`.
Countable completeness gives `Filter.Product.piEquivOfCountable` for countable
coordinate types. For finite coordinate types no completeness assumption on the
filter is needed, giving `Filter.Product.piEquiv`.

The representative application and inverse laws describe the construction without
unfolding a quotient. Naturality is with respect to arbitrary fibrewise functions,
with independent source and target universes. No algebraic structure, inhabited
fibres or properness of the filter is required.

The stock quotient-Pi construction uses the pointwise family of setoids. Here the
source relation is uniform eventual equality of rows; intersection closure converts
coordinatewise eventual equality to that relation. For families constant in the
row index this specializes to the comparison between germs of functions and
functions of germs.

## References

The construction uses the existing dependent reduced-product carrier and fibrewise
map. Its proofs reuse Mathlib's quotient representative and Pi-induction API,
eventual quantification, cardinal bounds, and equivalence packaging. The filter
intersection and cardinal-size APIs are due to Yury Kudryashov, Josha Dekker and
Joël Riou. In particular, the representative choice in `Quotient.induction_on_pi`
is not implemented again.
-/

@[expose] public section

universe u v w z

namespace Filter
namespace Product

variable {ι : Type u} {κ : Type v} (D : Filter ι) (R : ι → κ → Type w)

/-- Comparison from the reduced product of function types to the family of
coordinate reduced products, induced by coordinate evaluation. -/
def piComparison :
    D.Product (fun i => ∀ j, R i j) → ∀ j, D.Product (fun i => R i j) :=
  fun x j => map D (fun i (f : ∀ k, R i k) => f j) x

/-- The comparison evaluates a represented matrix one column at a time. -/
@[simp]
theorem piComparison_coe (f : ∀ i j, R i j) (j : κ) :
    piComparison D R (f : D.Product (fun i => ∀ j, R i j)) j =
      ((fun i => f i j) : D.Product (fun i => R i j)) := by
  exact map_coe D (fun i (r : ∀ k, R i k) => r j) f

/-- Every family of coordinate classes has a represented matrix as a preimage.
This uses global representatives of the supplied quotient points, not an
inhabitation assumption on the fibre family. -/
theorem piComparison_surjective : Function.Surjective (piComparison D R) := by
  intro y
  refine Quotient.induction_on_pi y ?_
  intro a
  let f : ∀ i j, R i j := fun i j => a j i
  refine ⟨(f : D.Product (fun i => ∀ j, R i j)), ?_⟩
  funext j
  exact piComparison_coe D R f j

/-- Intersection closure below `c` makes the comparison injective when the
coordinate type has cardinality less than `c`, independently of its universe. -/
theorem piComparison_injective_of_hasCardinalLT
    {c : Cardinal.{u}} [CardinalInterFilter D c] (hκ : HasCardinalLT κ c) :
    Function.Injective (piComparison D R) := by
  intro x y h
  obtain ⟨f, rfl⟩ := coe_surjective D (fun i => ∀ j, R i j) x
  obtain ⟨g, rfl⟩ := coe_surjective D (fun i => ∀ j, R i j) y
  apply (coe_eq f g).2
  have hcol : ∀ j, ∀ᶠ i in D, f i j = g i j := by
    intro j
    apply (coe_eq (fun i => f i j) (fun i => g i j)).1
    exact (piComparison_coe D R f j).symm.trans
      ((congrFun h j).trans (piComparison_coe D R g j))
  -- The range lives in the row universe even when the coordinates do not.
  let s : κ → Set ι := fun j => {i | f i j = g i j}
  let S : Set (Set ι) := Set.range s
  have hS : HasCardinalLT S c :=
    hκ.of_surjective (Set.rangeFactorization s) Set.rangeFactorization_surjective
  have hsmall : Cardinal.mk S < c := (hasCardinalLT_iff_cardinal_mk_lt S c).1 hS
  have hinter : ⋂₀ S ∈ D := (cardinal_sInter_mem hsmall).2 (by
    rintro _ ⟨j, rfl⟩
    exact hcol j)
  exact Filter.mem_of_superset hinter fun i hi => funext fun j => hi (s j) ⟨j, rfl⟩

/-- Finite coordinate quantification commutes with eventual equality, making the
comparison injective without any assumption on the filter or fibres. -/
theorem piComparison_injective [Finite κ] : Function.Injective (piComparison D R) := by
  let := Filter.cardinalInterFilter_aleph0 D
  exact piComparison_injective_of_hasCardinalLT D R
    ((hasCardinalLT_aleph0_iff κ).2 inferInstance)

/-- Reduced products preserve finite products of dependent fibre types. -/
theorem piComparison_bijective [Finite κ] : Function.Bijective (piComparison D R) :=
  ⟨piComparison_injective D R, piComparison_surjective D R⟩

/-- The equivalence between a reduced product of function types on a finite
coordinate index and the family of coordinate reduced products. -/
noncomputable def piEquiv [Finite κ] :
    D.Product (fun i => ∀ j, R i j) ≃ ∀ j, D.Product (fun i => R i j) :=
  Equiv.ofBijective (piComparison D R) (piComparison_bijective D R)

/-- The forward function of the finite-product equivalence is the comparison. -/
@[simp]
theorem piEquiv_apply [Finite κ] (x : D.Product (fun i => ∀ j, R i j)) :
    piEquiv D R x = piComparison D R x :=
  rfl

/-- The inverse of the finite-product equivalence transposes supplied global
representatives of the coordinate classes. -/
@[simp]
theorem piEquiv_symm_coe [Finite κ] (f : ∀ j i, R i j) :
    (piEquiv D R).symm (fun j => (f j : D.Product (fun i => R i j))) =
      (((fun i j => f j i) : ∀ i j, R i j) : D.Product (fun i => ∀ j, R i j)) := by
  apply piComparison_injective D R
  have hleft :
      piComparison D R ((piEquiv D R).symm
        (fun j => (f j : D.Product (fun i => R i j)))) =
        fun j => (f j : D.Product (fun i => R i j)) :=
    (piEquiv D R).apply_symm_apply _
  have hright :
      piComparison D R
        (((fun i j => f j i) : ∀ i j, R i j) : D.Product (fun i => ∀ j, R i j)) =
        fun j => (f j : D.Product (fun i => R i j)) := by
    funext j
    exact piComparison_coe D R (fun i j => f j i) j
  exact hleft.trans hright.symm

/-- Naturality of the comparison under arbitrary fibrewise functions. This does
not require a finite coordinate index. -/
theorem piComparison_map (S : ι → κ → Type z) (h : ∀ i j, R i j → S i j)
    (x : D.Product (fun i => ∀ j, R i j)) :
    piComparison D S (map D (fun i (f : ∀ j, R i j) j => h i j (f j)) x) =
      fun j => map D (fun i => h i j) (piComparison D R x j) := by
  funext j
  simp only [piComparison, map_map]

/-- The inverse finite-product equivalence is natural under arbitrary fibrewise
functions, including when the reduced-product types are empty. -/
theorem map_piEquiv_symm [Finite κ] (S : ι → κ → Type z)
    (h : ∀ i j, R i j → S i j) (y : ∀ j, D.Product (fun i => R i j)) :
    map D (fun i (f : ∀ j, R i j) j => h i j (f j)) ((piEquiv D R).symm y) =
      (piEquiv D S).symm (fun j => map D (fun i => h i j) (y j)) := by
  apply piComparison_injective D S
  have hR : piComparison D R ((piEquiv D R).symm y) = y :=
    (piEquiv D R).apply_symm_apply y
  have hS :
      piComparison D S ((piEquiv D S).symm
        (fun j => map D (fun i => h i j) (y j))) =
        fun j => map D (fun i => h i j) (y j) :=
    (piEquiv D S).apply_symm_apply _
  exact (piComparison_map D R S h ((piEquiv D R).symm y)).trans
    ((congrArg (fun q : ∀ j, D.Product (fun i => R i j) =>
      fun j => map D (fun i => h i j) (q j)) hR).trans hS.symm)

/-- The equivalence between a reduced product of function types with fewer than
`c` coordinates and the family of coordinate reduced products, for a filter
closed under intersections of fewer than `c` sets. -/
noncomputable def piEquivOfHasCardinalLT
    {c : Cardinal.{u}} [CardinalInterFilter D c] (hκ : HasCardinalLT κ c) :
    D.Product (fun i => ∀ j, R i j) ≃ ∀ j, D.Product (fun i => R i j) :=
  Equiv.ofBijective (piComparison D R)
    ⟨piComparison_injective_of_hasCardinalLT D R hκ, piComparison_surjective D R⟩

/-- The forward function of the cardinal-bounded product equivalence is the comparison. -/
@[simp]
theorem piEquivOfHasCardinalLT_apply
    {c : Cardinal.{u}} [CardinalInterFilter D c] (hκ : HasCardinalLT κ c)
    (x : D.Product (fun i => ∀ j, R i j)) :
    piEquivOfHasCardinalLT D R hκ x = piComparison D R x :=
  rfl

/-- On a finite coordinate type, the cardinal-bounded equivalence equals the
finite-product equivalence as equivalence data. -/
theorem piEquivOfHasCardinalLT_eq_piEquiv
    {c : Cardinal.{u}} [CardinalInterFilter D c] (hκ : HasCardinalLT κ c) [Finite κ] :
    piEquivOfHasCardinalLT D R hκ = piEquiv D R := by
  apply Equiv.ext
  intro x
  rfl

/-- Countable intersection closure makes the comparison injective for a
countable coordinate type, independently of its universe. -/
theorem piComparison_injective_of_countable [CountableInterFilter D] [Countable κ] :
    Function.Injective (piComparison D R) := by
  have hκ : HasCardinalLT κ (Cardinal.aleph 1 : Cardinal.{u}) := by
    simpa only [HasCardinalLT, Cardinal.lift_aleph, Ordinal.lift_one,
      Cardinal.lt_aleph_one_iff, Cardinal.lift_le_aleph0] using
        (Cardinal.mk_le_aleph0_iff.2 (inferInstance : Countable κ))
  exact piComparison_injective_of_hasCardinalLT D R hκ

/-- The equivalence between a reduced product of function types on a countable
coordinate type and the family of coordinate reduced products, for a countably
complete filter. -/
noncomputable def piEquivOfCountable [CountableInterFilter D] [Countable κ] :
    D.Product (fun i => ∀ j, R i j) ≃ ∀ j, D.Product (fun i => R i j) :=
  Equiv.ofBijective (piComparison D R)
    ⟨piComparison_injective_of_countable D R, piComparison_surjective D R⟩

/-- The forward function of the countable-product equivalence is the comparison. -/
@[simp]
theorem piEquivOfCountable_apply [CountableInterFilter D] [Countable κ]
    (x : D.Product (fun i => ∀ j, R i j)) :
    piEquivOfCountable D R x = piComparison D R x :=
  rfl

/-- On a finite coordinate type, the countable-product equivalence equals the
finite-product equivalence as equivalence data. -/
theorem piEquivOfCountable_eq_piEquiv [CountableInterFilter D] [Finite κ] :
    piEquivOfCountable D R = piEquiv D R := by
  apply Equiv.ext
  intro x
  rfl

end Product
end Filter
