/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Reduced commutative semirings under localization

Reducedness passes to an arbitrary localization. The source and target may lie in
independent universes, and neither additive inverses nor nontriviality are required.
The proof uses commutation of ideal radicals with localization, applied to the zero ideal.

## References

* Mathlib's `IsLocalization.map_radical`, in
  [Localization.Ideal](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Localization/Ideal.lean).
* Andrew Yang's `isReduced_localizationPreserves`, in
  [LocalProperties.Reduced](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/LocalProperties/Reduced.lean).
* The independent-universe commutative-ring formulation `IsLocalization.isReduced` in
  [SchemeProperties.Reduced](https://github.com/FormalFrontier/scheme-properties/blob/54d353b68e189ebe60efb9f1d8518ca0b16c2aef/SchemeProperties/Reduced.lean).
-/

@[expose] public section

universe u v

/-- A localization of a reduced commutative semiring is reduced.

This extends Mathlib's `isReduced_localizationPreserves` and the commutative-ring
formulation in `SchemeProperties.Reduced` to semirings in independent universes. -/
theorem IsReduced.of_isLocalization {R : Type u} [CommSemiring R]
    (M : Submonoid R) (A : Type v) [CommSemiring A] [Algebra R A]
    [IsLocalization M A] [IsReduced R] : IsReduced A := by
  apply nilradical_eq_bot_iff.mp
  change (⊥ : Ideal A).radical = ⊥
  have hR : (⊥ : Ideal R).radical = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
  simpa only [hR, Ideal.map_bot] using
    (IsLocalization.map_radical M A (⊥ : Ideal R)).symm
