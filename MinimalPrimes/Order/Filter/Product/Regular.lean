/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Regular.Defs
public import MinimalPrimes.Order.Filter.Basic
public import MinimalPrimes.Order.Filter.Product

/-!
# Regular elements of dependent reduced products

A total dependent section represents a left-regular, right-regular, or regular
element precisely when its values have the corresponding property eventually.
Only fibrewise multiplication is required, and the filter and the index and fibre
universes are arbitrary.

For necessity, apply anchored section reflection to pairs whose products with the
given section agree. Quotient cancellation makes the two components equal eventually.
The supplied section gives a fallback collision pair, including at coordinates ignored
by the filter, without a separate nonemptiness assumption. Sufficiency cancels on the
intersection of two eventual sets.

## References

The collision argument generalizes the constant-family formalization in
`MinimalPrimes.Order.Filter.Germ.Regular` and uses section reflection from
`MinimalPrimes.Order.Filter.Basic`. The carrier and quotient operations reuse
Mathlib's `Order.Filter.Germ.Basic` and Amelia Livingston's multiplicative-congruence
API. Regularity uses Damiano Testa's `Mathlib.Algebra.Regular.Defs`; the related
pointwise criteria are in Eric Wieser's `Mathlib.Algebra.Regular.Pi`.
-/

@[expose] public section

universe u v

namespace Filter.Product

variable {ι : Type u} {K : ι → Type v} [∀ i, Mul (K i)]

/-- Left multiplication by a dependent product is injective exactly when left multiplication by
its representative is injective eventually. -/
theorem isLeftRegular_coe_iff (D : Filter ι) (f : ∀ i, K i) :
    IsLeftRegular (R := D.Product K) (f : D.Product K) ↔ ∀ᶠ i in D, IsLeftRegular (f i) := by
  constructor
  · intro hf
    have hreg : ∀ᶠ i in D,
        ∀ p : {p : K i × K i // f i * p.1 = f i * p.2}, p.1.1 = p.1.2 := by
      apply (Filter.eventually_forall_iff_forall_section
        (R := fun i => {p : K i × K i // f i * p.1 = f i * p.2})
        (D := D) (P := fun _ p => p.1.1 = p.1.2)
        (fun i => ⟨(f i, f i), rfl⟩)).2
      intro p
      let x : ∀ i, K i := fun i => (p i).1.1
      let y : ∀ i, K i := fun i => (p i).1.2
      have hmul : ((fun i => f i * x i) : D.Product K) =
          ((fun i => f i * y i) : D.Product K) :=
        (coe_eq (F := D) (fun i => f i * x i) (fun i => f i * y i)).2
          (Eventually.of_forall fun i => (p i).2)
      have hxy : (x : D.Product K) = (y : D.Product K) := hf hmul
      exact (coe_eq (F := D) x y).1 hxy
    exact hreg.mono fun i hi x y hxy => hi ⟨(x, y), hxy⟩
  · intro hf a b
    refine Quotient.inductionOn₂' a b ?_
    intro x y hxy
    have hmul : ∀ᶠ i in D, f i * x i = f i * y i :=
      (coe_eq (F := D) (fun i => f i * x i) (fun i => f i * y i)).1 hxy
    exact (coe_eq (F := D) x y).2 ((hf.and hmul).mono fun i hi => hi.1 hi.2)

/-- Right multiplication by a dependent product is injective exactly when right multiplication
by its representative is injective eventually. -/
theorem isRightRegular_coe_iff (D : Filter ι) (f : ∀ i, K i) :
    IsRightRegular (R := D.Product K) (f : D.Product K) ↔ ∀ᶠ i in D, IsRightRegular (f i) := by
  constructor
  · intro hf
    have hreg : ∀ᶠ i in D,
        ∀ p : {p : K i × K i // p.1 * f i = p.2 * f i}, p.1.1 = p.1.2 := by
      apply (Filter.eventually_forall_iff_forall_section
        (R := fun i => {p : K i × K i // p.1 * f i = p.2 * f i})
        (D := D) (P := fun _ p => p.1.1 = p.1.2)
        (fun i => ⟨(f i, f i), rfl⟩)).2
      intro p
      let x : ∀ i, K i := fun i => (p i).1.1
      let y : ∀ i, K i := fun i => (p i).1.2
      have hmul : ((fun i => x i * f i) : D.Product K) =
          ((fun i => y i * f i) : D.Product K) :=
        (coe_eq (F := D) (fun i => x i * f i) (fun i => y i * f i)).2
          (Eventually.of_forall fun i => (p i).2)
      have hxy : (x : D.Product K) = (y : D.Product K) := hf hmul
      exact (coe_eq (F := D) x y).1 hxy
    exact hreg.mono fun i hi x y hxy => hi ⟨(x, y), hxy⟩
  · intro hf a b
    refine Quotient.inductionOn₂' a b ?_
    intro x y hxy
    have hmul : ∀ᶠ i in D, x i * f i = y i * f i :=
      (coe_eq (F := D) (fun i => x i * f i) (fun i => y i * f i)).1 hxy
    exact (coe_eq (F := D) x y).2 ((hf.and hmul).mono fun i hi => hi.1 hi.2)

/-- A dependent product is regular exactly when its representative is regular eventually. -/
theorem isRegular_coe_iff (D : Filter ι) (f : ∀ i, K i) :
    IsRegular (R := D.Product K) (f : D.Product K) ↔ ∀ᶠ i in D, IsRegular (f i) := by
  constructor
  · intro hf
    exact (((isLeftRegular_coe_iff D f).1 hf.left).and
      ((isRightRegular_coe_iff D f).1 hf.right)).mono fun _ hi => ⟨hi.1, hi.2⟩
  · intro hf
    exact ⟨(isLeftRegular_coe_iff D f).2 (hf.mono fun _ hi => hi.left),
      (isRightRegular_coe_iff D f).2 (hf.mono fun _ hi => hi.right)⟩

end Filter.Product
