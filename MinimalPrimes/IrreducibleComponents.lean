/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Irreducible components of a principal zero locus in a UFD

This file composes the normalized-factor/minimal-prime equivalence with mathlib's
minimal-prime/irreducible-component correspondence for the zero-locus subspace
of `PrimeSpectrum R`. The codomain is order-dual; the result is an `Equiv`, not a
homeomorphism or a classification of arbitrary ideals.
-/

@[expose] public section

noncomputable section

open TopologicalSpace UniqueFactorizationMonoid

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [UniqueFactorizationMonoid R]
  [NormalizationMonoid R]

/-- The normalized factor values of a nonzero element are equivalent to the
order-dual irreducible components of the zero-locus subspace of its principal
ideal in `PrimeSpectrum R`. Composes `normalizedFactorsEquivMinimalPrimes` with
mathlib's `minimalPrimes.equivIrreducibleComponents` and forgets its order
structure with `toEquiv`; the inverse is noncomputable. -/
def normalizedFactorsEquivIrreducibleComponents {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃
      (irreducibleComponents (PrimeSpectrum.zeroLocus (span {f} : Set R)))ᵒᵈ :=
  (normalizedFactorsEquivMinimalPrimes hf).trans
    (minimalPrimes.equivIrreducibleComponents (span {f})).toEquiv

end Ideal
