/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Principal

/-! # README examples: generic classification and the forward map -/

open UniqueFactorizationMonoid

noncomputable section
universe u

noncomputable local instance readmeGenericNormalization (M : Type*) [CommMonoidWithZero M]
    [UniqueFactorizationMonoid M] : StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

variable {R : Type u} [CommRing R] [UniqueFactorizationMonoid R]

private theorem readme_classification {f : R} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private def readme_minimalPrimes {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf

private theorem readme_forwardMap {f : R} (hf : f ≠ 0)
    (p : {p // p ∈ normalizedFactors f}) :
    (Ideal.normalizedFactorsEquivMinimalPrimes hf p).1 = Ideal.span {p.1} := by
  simp
