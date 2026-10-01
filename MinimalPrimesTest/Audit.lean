/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes

/-!
# Aggregate-import regression checks

Stored generic and integer tests exercise the algebraic and geometric interfaces,
their normalization scope, and boundary cases through the public root import.
-/

open TopologicalSpace UniqueFactorizationMonoid

noncomputable section

section GenericNormalization

-- A generic UFD need not export a normalization choice. Callers can make the
-- conventional noncomputable choice locally; the public API then uses it.
noncomputable local instance auditStrongNormalizationMonoid
    (M : Type*) [CommMonoidWithZero M] [UniqueFactorizationMonoid M] :
    StrongNormalizationMonoid M :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

universe u

variable {R : Type u} [CommRing R] [UniqueFactorizationMonoid R]

-- The aggregate import exposes the algebraic classification.
private theorem generic_classification {f : R} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

-- The aggregate import also exposes the geometric equivalence.
private noncomputable def generic_components {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃
      (irreducibleComponents
        (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set R)))ᵒᵈ :=
  Ideal.normalizedFactorsEquivIrreducibleComponents hf

-- A unit has no factors and its unit ideal has no minimal primes.
private theorem unit_boundary {u : R} (hu : IsUnit u) :
    (Ideal.span {u}).minimalPrimes = ∅ ∧ normalizedFactors u = 0 := by
  exact ⟨by rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.minimalPrimes_top],
    UniqueFactorizationMonoid.normalizedFactors_of_isUnit hu⟩

-- Repeated factors retain their multiplicity in the multiset. The public
-- classification uses only membership in this multiset and hence forgets it.
private theorem repeated_factor_boundary {p : R} (hp : Irreducible p) (n : ℕ) :
    normalizedFactors (p ^ n) = Multiset.replicate n (normalize p) :=
  hp.normalizedFactors_pow n

-- The nonzero hypothesis is necessary: zero has no normalized factors, while
-- a domain's zero ideal is its unique minimal prime.
private theorem zero_boundary [IsDomain R] : (Ideal.span ({0} : Set R)).minimalPrimes = {⊥} ∧
    normalizedFactors (0 : R) = 0 := by
  exact ⟨by simpa using (IsDomain.minimalPrimes_eq_singleton_bot (R := R)),
    UniqueFactorizationMonoid.normalizedFactors_zero⟩

-- The nonzero hypothesis also excludes the subsingleton UFM boundary.
omit [UniqueFactorizationMonoid R] in
private theorem subsingleton_boundary [Subsingleton R] {f : R} (hf : f ≠ 0) : False :=
  hf (Subsingleton.elim f 0)

end GenericNormalization

section IntegerDownstream

-- These downstream checks deliberately use the ordinary normalization instance
-- exported for ℤ; no local normalization override is in scope.
private theorem integer_classification {f : ℤ} (hf : f ≠ 0) :
    (Ideal.span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = Ideal.span {p}} :=
  Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hf

private noncomputable def integer_minimal_primes {f : ℤ} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (Ideal.span {f}).minimalPrimes :=
  Ideal.normalizedFactorsEquivMinimalPrimes hf

private noncomputable def integer_components {f : ℤ} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃
      (irreducibleComponents
        (PrimeSpectrum.zeroLocus (Ideal.span {f} : Set ℤ)))ᵒᵈ :=
  Ideal.normalizedFactorsEquivIrreducibleComponents hf

end IntegerDownstream

#print axioms Ideal.minimalPrimes_span_singleton_eq_normalizedFactors
#print axioms Ideal.normalizedFactorsEquivMinimalPrimes
#print axioms Ideal.normalizedFactorsEquivMinimalPrimes_apply
#print axioms Ideal.normalizedFactorsEquivIrreducibleComponents
