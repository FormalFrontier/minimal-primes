/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import MinimalPrimes.RingTheory.Localization.Reduced

/-!
# Field localizations at prime ideals

For an arbitrary prime ideal `q` of a commutative semiring `R`, a localization `A`
at `q` satisfies `IsField A` exactly when `q` is minimal and `A` is reduced.
Here `IsField` includes semifields: additive inverses are not required.
Only the corollary assumes that the base is reduced.

The maximal ideal of `A` contracts to `q`. If `A` is a field, its zero maximal ideal
is minimal, so the localization correspondence gives minimality of `q`.
Conversely, at a minimal prime, the extended prime is the radical of zero;
reducedness makes this maximal ideal zero.

## Boundaries

For integers localized at `(2)`, reducedness holds but minimality fails; this is
not the quotient `ℤ / 2ℤ`. Minimality alone is insufficient for nonreduced targets:
in `ℤ / 4ℤ`, the unique prime `(2)` is minimal and its complement consists of units,
so localizing there leaves the nonzero square-zero element `2`. These boundary
arguments do not require a new model of localization. The zero semiring has no
prime ideal, so the hypotheses already exclude a trivial localization.

## References

The proof composes Mathlib's maximal-ideal criterion for `IsField` with Andrew Yang's
[minimal-prime localization correspondence](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean).
The ring-geometric criterion for reduced scheme stalks in
[SchemeProperties.NormalValuationStalk](https://github.com/FormalFrontier/scheme-properties/blob/54d353b68e189ebe60efb9f1d8518ca0b16c2aef/SchemeProperties/NormalValuationStalk.lean)
is related via affine stalks and coheight, rather than a statement about arbitrary
commutative-semiring localizations.
-/

@[expose] public section

universe u v

namespace IsLocalization.AtPrime

variable {R : Type u} [CommSemiring R] (A : Type v) [CommSemiring A] [Algebra R A]
variable (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime A q]

/-- A localization at a prime ideal satisfies `IsField` precisely when the prime is
minimal and the localization is reduced. This uses Mathlib's minimal-prime
localization correspondence and its zero-maximal-ideal criterion for `IsField`.
For semirings, `IsField` expresses semifieldhood, without requiring additive inverses. -/
theorem isField_iff_mem_minimalPrimes_and_isReduced :
    IsField A ↔ q ∈ minimalPrimes R ∧ IsReduced A := by
  letI : IsLocalRing A := isLocalRing A q
  constructor
  · intro h
    have hm : IsLocalRing.maximalIdeal A = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp h
    constructor
    · have hmin : IsLocalRing.maximalIdeal A ∈
          ((⊥ : Ideal R).map (algebraMap R A)).minimalPrimes := by
        rw [Ideal.map_bot, ← hm, Ideal.minimalPrimes_eq_subsingleton_self]
        exact Set.mem_singleton _
      rw [IsLocalization.minimalPrimes_map q.primeCompl A, Set.mem_preimage,
        under_maximalIdeal A q] at hmin
      exact hmin
    · apply nilradical_eq_bot_iff.mp
      exact le_antisymm
        ((nilradical_le_prime (IsLocalRing.maximalIdeal A)).trans_eq hm) bot_le
  · rintro ⟨hq, hred⟩
    apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    have hr := radical_map_of_mem_minimalPrimes A q (⊥ : Ideal R) hq
    rw [Ideal.map_bot, map_eq_maximalIdeal q A] at hr
    exact hr.symm.trans (nilradical_eq_bot_iff.mpr hred)

/-- Over a reduced commutative semiring, localization at a prime satisfies `IsField`
exactly when the prime is minimal. Reducedness of the localization follows from
`IsReduced.of_isLocalization`. -/
theorem isField_iff_mem_minimalPrimes [IsReduced R] :
    IsField A ↔ q ∈ minimalPrimes R := by
  have hred : IsReduced A := IsReduced.of_isLocalization q.primeCompl A
  exact (isField_iff_mem_minimalPrimes_and_isReduced A q).trans
    ⟨And.left, fun hq => ⟨hq, hred⟩⟩

end IsLocalization.AtPrime
