/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import MinimalPrimes.Order.Filter.Product.Module
public import MinimalPrimes.Order.Filter.Product.Regular

/-!
# Torsion-free semimodules over dependent reduced products

A represented scalar acts injectively precisely when its fibre actions are
injective eventually. This uses the existing coordinate-map criterion, including
its empty-total-source alternative; a zero section excludes that alternative.

The torsion-free criterion concerns the two reduced products with the named
semimodule of the given fibre actions. Torsion-freeness means full injectivity for
every two-sided regular scalar, not merely trivial scalar annihilators.

Preservation combines eventual fibre torsion-freeness with the existing
represented-scalar regularity criterion. For reflection, sections of the regular
scalar subtypes have regular quotient classes. The section-reflection theorem
then exchanges quantification over these sections with eventual fibrewise
quantification. The regular scalar `1` supplies the required total section,
including over zero semirings and at empty indices.

## References

The regular-action and modern torsion-free interfaces are Mathlib's. The proof of
the represented-scalar readout uses the existing dependent coordinate-map
injectivity theorem, not a new quotient or collision argument.
-/

@[expose] public section

universe u v w

namespace Filter.Product

variable {ι : Type u} (F : Filter ι) (R : ι → Type v) (M : ι → Type w)

section RegularAction

variable [∀ i, Zero (M i)] [∀ i, SMul (R i) (M i)]

attribute [local instance] smul

/-- A represented scalar has injective action iff its fibre actions are eventually injective. -/
theorem isSMulRegular_coe_iff (r : ∀ i, R i) :
    @IsSMulRegular (F.Product R) (F.Product M) (smul F M R) (r : F.Product R) ↔
      ∀ᶠ i in F, IsSMulRegular (M i) (r i) := by
  change Function.Injective (fun x : F.Product M =>
    ((· • ·) : F.Product R → F.Product M → F.Product M) (r : F.Product R) x) ↔ _
  rw [smul_coe_eq_map, map_injective_iff]
  constructor
  · rintro (h | h)
    · exact (h.false (fun _ => 0)).elim
    · exact h
  · exact Or.inr

end RegularAction

/-- Torsion-freeness over the reduced product of varying scalar semirings is
 equivalent to eventual fibre torsion-freeness, for the given fibre semimodules. -/
theorem isTorsionFree_iff
    [s : ∀ i, Semiring (R i)] [a : ∀ i, AddCommMonoid (M i)]
    [p : ∀ i, Module (R i) (M i)] :
    @Module.IsTorsionFree (F.Product R) (F.Product M)
      (instSemiring (F := F) (K := R)) (addCommMonoid F M)
      (module (s := s) (a := a) (p := p) F M R) ↔
        ∀ᶠ i in F, @Module.IsTorsionFree (R i) (M i) (s i) (a i) (p i) := by
  let := addCommMonoid F M
  let := module (s := s) (a := a) (p := p) F M R
  constructor
  · intro h
    let := h
    have hsections : ∀ ρ : ∀ i, {r : R i // IsRegular r},
        ∀ᶠ i in F, IsSMulRegular (M i) (ρ i).1 := by
      intro ρ
      apply (isSMulRegular_coe_iff F R M (fun i => (ρ i).1)).mp
      exact Module.IsTorsionFree.isSMulRegular
        ((isRegular_coe_iff F _).mpr (Eventually.of_forall fun i => (ρ i).2))
    -- The regular scalar 1 supplies a section even for zero scalar semirings.
    have hregular := (eventually_forall_iff_forall_section
      (D := F) (P := fun i (r : {r : R i // IsRegular r}) => IsSMulRegular (M i) r.1)
      (fun i => (⟨1, isRegular_one⟩ : {r : R i // IsRegular r}))).mpr hsections
    exact hregular.mono fun i hi => ⟨fun {r} hr => hi ⟨r, hr⟩⟩
  · intro h
    constructor
    intro r hr
    induction r using inductionOn F R with | h r =>
      apply (isSMulRegular_coe_iff F R M r).mpr
      filter_upwards [h, (isRegular_coe_iff F r).mp hr] with i hi hri
      let := hi
      exact hri.isSMulRegular

end Filter.Product
