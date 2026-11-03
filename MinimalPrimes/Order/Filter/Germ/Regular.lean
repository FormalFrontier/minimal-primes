/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Regular elements of filter germs

A function represents a left-regular, right-regular, or regular germ precisely when
its values have the corresponding property eventually. The codomain needs only a
multiplication; the filter may be improper and the index or codomain may be empty.

For necessity, choose a pair with equal products at every coordinate where
cancellation fails, and use the given function value for both entries elsewhere.
This avoids choosing an element of the codomain independently of the index.
Sufficiency cancels representatives on the intersection of two eventual sets.

## References

The representation and cancellation argument use Mathlib's
`Mathlib.Order.Filter.Germ.Basic` quotient, induction, and multiplication API.
Regularity uses `Mathlib.Algebra.Regular.Defs`; the related pointwise function
criteria are in `Mathlib.Algebra.Regular.Pi`.
-/

@[expose] public section

universe u v

namespace Filter.Germ

variable {ι : Type u} {M : Type v} [Mul M]

/-- Left multiplication by a germ is injective exactly when left multiplication by
its representative is injective eventually. -/
theorem isLeftRegular_coe_iff (D : Filter ι) (f : ι → M) :
    IsLeftRegular (f : Germ D M) ↔ ∀ᶠ i in D, IsLeftRegular (f i) := by
  classical
  constructor
  · intro hf
    have hex : ∀ i, ∃ x y : M,
        f i * x = f i * y ∧ (x = y → IsLeftRegular (f i)) := by
      intro i
      by_cases hi : IsLeftRegular (f i)
      · exact ⟨f i, f i, rfl, fun _ => hi⟩
      · have hbad : ∃ x y : M, f i * x = f i * y ∧ x ≠ y := by
          simpa only [IsLeftRegular, Function.Injective, not_forall, exists_prop] using hi
        obtain ⟨x, y, hxy, hne⟩ := hbad
        exact ⟨x, y, hxy, fun h => (hne h).elim⟩
    let x : ι → M := fun i => (hex i).choose
    let y : ι → M := fun i => (hex i).choose_spec.choose
    have hspec (i) : f i * x i = f i * y i ∧ (x i = y i → IsLeftRegular (f i)) :=
      (hex i).choose_spec.choose_spec
    have hmul : (f : Germ D M) * (x : Germ D M) = (f : Germ D M) * (y : Germ D M) :=
      coe_eq.2 (Eventually.of_forall fun i => (hspec i).1)
    exact (coe_eq.1 (hf hmul)).mono fun i hi => (hspec i).2 hi
  · intro hf a b
    refine inductionOn₂ a b ?_
    intro x y hxy
    exact coe_eq.2 ((hf.and (coe_eq.1 hxy)).mono fun i hi => hi.1 hi.2)

/-- Right multiplication by a germ is injective exactly when right multiplication
by its representative is injective eventually. -/
theorem isRightRegular_coe_iff (D : Filter ι) (f : ι → M) :
    IsRightRegular (f : Germ D M) ↔ ∀ᶠ i in D, IsRightRegular (f i) := by
  classical
  constructor
  · intro hf
    have hex : ∀ i, ∃ x y : M,
        x * f i = y * f i ∧ (x = y → IsRightRegular (f i)) := by
      intro i
      by_cases hi : IsRightRegular (f i)
      · exact ⟨f i, f i, rfl, fun _ => hi⟩
      · have hbad : ∃ x y : M, x * f i = y * f i ∧ x ≠ y := by
          simpa only [IsRightRegular, Function.Injective, not_forall, exists_prop] using hi
        obtain ⟨x, y, hxy, hne⟩ := hbad
        exact ⟨x, y, hxy, fun h => (hne h).elim⟩
    let x : ι → M := fun i => (hex i).choose
    let y : ι → M := fun i => (hex i).choose_spec.choose
    have hspec (i) : x i * f i = y i * f i ∧ (x i = y i → IsRightRegular (f i)) :=
      (hex i).choose_spec.choose_spec
    have hmul : (x : Germ D M) * (f : Germ D M) = (y : Germ D M) * (f : Germ D M) :=
      coe_eq.2 (Eventually.of_forall fun i => (hspec i).1)
    exact (coe_eq.1 (hf hmul)).mono fun i hi => (hspec i).2 hi
  · intro hf a b
    refine inductionOn₂ a b ?_
    intro x y hxy
    exact coe_eq.2 ((hf.and (coe_eq.1 hxy)).mono fun i hi => hi.1 hi.2)

/-- A germ is regular exactly when its representative is regular eventually. -/
theorem isRegular_coe_iff (D : Filter ι) (f : ι → M) :
    IsRegular (f : Germ D M) ↔ ∀ᶠ i in D, IsRegular (f i) := by
  simp only [_root_.isRegular_iff, isLeftRegular_coe_iff, isRightRegular_coe_iff,
    eventually_and]

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
