/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Principal
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Direct algebraic-leaf client

Check the public classification and factor equivalence through the principal-ideal
leaf alone, both with a caller-supplied generic normalization and with the
ordinary integer instance. Check the forward map by `apply` and simplification.
-/

noncomputable section

open UniqueFactorizationMonoid

section GenericNormalization

noncomputable local instance leafStrongNormalizationMonoid
    (M : Type*) [CommMonoidWithZero M] [UniqueFactorizationMonoid M] :
    StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

universe u

variable {R : Type u} [CommRing R] [UniqueFactorizationMonoid R]

private theorem generic_classification {f : R} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private noncomputable def generic_equiv {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf

private theorem generic_apply {f : R} (hf : f ≠ 0)
    (p : {p // p ∈ normalizedFactors f}) :
    (Ideal.normalizedFactorsEquivMinimalPrimes hf p).1 = Ideal.span {p.1} := by
  apply Ideal.normalizedFactorsEquivMinimalPrimes_apply

end GenericNormalization

section IntegerNormalization

private theorem integer_classification {f : ℤ} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private noncomputable def integer_equiv {f : ℤ} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf

private theorem integer_apply {f : ℤ} (hf : f ≠ 0)
    (p : {p // p ∈ normalizedFactors f}) :
    (Ideal.normalizedFactorsEquivMinimalPrimes hf p).1 = Ideal.span {p.1} := by
  simp

end IntegerNormalization
