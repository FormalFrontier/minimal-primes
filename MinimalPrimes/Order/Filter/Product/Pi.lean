/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Filter.Finite
public import MinimalPrimes.Order.Filter.Product
public import MinimalPrimes.Order.Filter.Product.Map

/-!
# Dependent reduced products and finite products

Coordinate evaluation induces a comparison from the reduced product of a family
of function types to the function type of the coordinate reduced products. This
comparison is surjective for every coordinate index type. For finite coordinate
indices it is bijective, giving `Filter.Product.piEquiv`.

The representative application and inverse laws describe the construction without
unfolding a quotient. Naturality is with respect to arbitrary fibrewise functions,
with independent source and target universes. No algebraic structure, inhabited
fibres or properness of the filter is required.

The stock quotient-Pi construction uses the pointwise family of setoids. Here the
source relation is uniform eventual equality of rows; the finite step converts
coordinatewise eventual equality to that relation. For families constant in the
row index this specializes to the comparison between germs of functions and
functions of germs.

## References

The construction uses the existing dependent reduced-product carrier and fibrewise
map. Its proofs reuse Mathlib's quotient representative and Pi-induction API,
finite eventual quantification, and equivalence packaging. In particular, the
representative choice in `Quotient.induction_on_pi` is not implemented again.
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

/-- Finite coordinate quantification commutes with eventual equality, making the
comparison injective without any assumption on the filter or fibres. -/
theorem piComparison_injective [Finite κ] : Function.Injective (piComparison D R) := by
  intro x y h
  obtain ⟨f, rfl⟩ := coe_surjective D (fun i => ∀ j, R i j) x
  obtain ⟨g, rfl⟩ := coe_surjective D (fun i => ∀ j, R i j) y
  apply (coe_eq f g).2
  have hcol : ∀ j, ∀ᶠ i in D, f i j = g i j := by
    intro j
    apply (coe_eq (fun i => f i j) (fun i => g i j)).1
    exact (piComparison_coe D R f j).symm.trans
      ((congrFun h j).trans (piComparison_coe D R g j))
  exact (Filter.eventually_all.mpr hcol).mono fun _ hi => funext hi

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

end Product
end Filter
