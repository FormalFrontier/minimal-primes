/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Principal
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Associated primes of a principal quotient

The associated primes of a principal quotient, as ideals of the base ring, are
the minimal primes above the defining ideal in a unique factorization ring.
No choice of normalized factors is needed in the statement, including when the
generator is zero.

Mathlib defines associated primes using radicals of element annihilators. This
comparison does not identify ideals of the base ring with ideals of the quotient;
an exact-annihilator interpretation is a separate question.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise 6.6.F
  (motivation for the principal-quotient example).
* Mathlib's associated-prime and minimal-prime APIs, and the existing
  `MinimalPrimes.Principal` classification of principal ideals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

@[expose] public section

universe u

namespace Ideal

private theorem mem_radical_colon_mk_iff {R : Type u} [CommRing R]
    (generator witness scalar : R) :
    scalar ∈ ((⊥ : Submodule R (R ⧸ span {generator})).colon
      {Ideal.Quotient.mk (span {generator}) witness}).radical ↔
      ∃ exponent : ℕ, generator ∣ scalar ^ exponent * witness := by
  rw [Ideal.mem_radical_iff]
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

private theorem colon_mk_mul_eq {R : Type u} [CommRing R] [IsCancelMulZero R]
    (factor witness : R) (hWitness : witness ≠ 0) :
    (⊥ : Submodule R (R ⧸ span {factor * witness})).colon
      {Ideal.Quotient.mk (span {factor * witness}) witness} = span {factor} := by
  ext scalar
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, mul_comm factor witness, mul_comm scalar witness,
    mul_dvd_mul_iff_left hWitness, Ideal.mem_span_singleton]

private theorem associatedPrimes_quotient_span_singleton_eq_minimalPrimes_of_ne_zero
    {R : Type u} [CommRing R] [UniqueFactorizationMonoid R] (f : R) (hf : f ≠ 0) :
    associatedPrimes R (R ⧸ span {f}) = (span {f}).minimalPrimes := by
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  ext primeIdeal
  constructor
  · intro hAssociated
    have : primeIdeal.IsPrime := hAssociated.isPrime
    have hGenerator : span {f} ≤ primeIdeal := by
      have hAnnihilator := hAssociated.annihilator_le
      rw [Submodule.annihilator_top, Ideal.annihilator_quotient] at hAnnihilator
      exact hAnnihilator
    obtain ⟨minimalIdeal, hMinimal, hBelow⟩ :=
      Ideal.exists_minimalPrimes_le hGenerator
    have hFactor := hMinimal
    rw [minimalPrimes_span_singleton_eq_normalizedFactors hf] at hFactor
    obtain ⟨primeFactor, hFactorMem, rfl⟩ := hFactor
    have hPrimeFactor : Prime primeFactor :=
      UniqueFactorizationMonoid.prime_of_normalized_factor primeFactor hFactorMem
    obtain ⟨witness, hWitness⟩ := hAssociated.2
    obtain ⟨witness, rfl⟩ :=
      Ideal.Quotient.mkₐ_surjective R (span {f}) witness
    simp only [Ideal.Quotient.mkₐ_eq_mk] at hWitness
    have hNotDivides : ¬ f ∣ witness := by
      intro hDivides
      have hOne : (1 : R) ∈ primeIdeal := by
        rw [hWitness, mem_radical_colon_mk_iff]
        exact ⟨0, by simpa using hDivides⟩
      exact hAssociated.isPrime.ne_top ((eq_top_iff_one primeIdeal).mpr hOne)
    have hPrimeMem : primeFactor ∈ primeIdeal :=
      hBelow (mem_span_singleton_self primeFactor)
    obtain ⟨primePower, hPrimePower⟩ :=
      (mem_radical_colon_mk_iff f witness primeFactor).mp (hWitness ▸ hPrimeMem)
    have hReverse : primeIdeal ≤ span {primeFactor} := by
      intro scalar hScalar
      by_contra hNotMem
      have hNotDividesPrime : ¬primeFactor ∣ scalar := by
        simpa only [mem_span_singleton] using hNotMem
      have hRelPrime : IsRelPrime primeFactor scalar :=
        hPrimeFactor.irreducible.isRelPrime_iff_not_dvd.mpr hNotDividesPrime
      obtain ⟨scalarPower, hScalarPower⟩ :=
        (mem_radical_colon_mk_iff f witness scalar).mp (hWitness ▸ hScalar)
      let : GCDMonoid R := UniqueFactorizationMonoid.toGCDMonoid R
      have hUnit : IsUnit (gcd (primeFactor ^ primePower) (scalar ^ scalarPower)) :=
        gcd_isUnit_iff_isRelPrime.mpr hRelPrime.pow
      have hDivides : f ∣ witness := by
        calc
          f ∣ gcd (primeFactor ^ primePower * witness)
              (scalar ^ scalarPower * witness) := dvd_gcd hPrimePower hScalarPower
          _ ∣ gcd (primeFactor ^ primePower) (scalar ^ scalarPower) * witness :=
            (gcd_mul_right' witness _ _).dvd
          _ ∣ witness := by
            simpa using (mul_dvd_mul_right (isUnit_iff_dvd_one.mp hUnit) witness)
      exact hNotDivides hDivides
    have hEqual : primeIdeal = span {primeFactor} := le_antisymm hReverse hBelow
    rw [hEqual]
    exact hMinimal
  · intro hMinimal
    have hFactor := hMinimal
    rw [minimalPrimes_span_singleton_eq_normalizedFactors hf] at hFactor
    obtain ⟨primeFactor, hFactorMem, rfl⟩ := hFactor
    have hPrimeFactor : (span {primeFactor} : Ideal R).IsPrime :=
      isPrime_span_singleton_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor primeFactor hFactorMem)
    obtain ⟨witness, hFactorization⟩ :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hFactorMem
    have hWitnessNonzero : witness ≠ 0 := by
      intro hZero
      apply hf
      rw [hFactorization, hZero, mul_zero]
    rw [hFactorization]
    exact ⟨hPrimeFactor, ⟨Ideal.Quotient.mk (span {primeFactor * witness}) witness,
      by rw [colon_mk_mul_eq primeFactor witness hWitnessNonzero,
        hPrimeFactor.radical]⟩⟩

/-- The associated primes of `R/(f)` as an `R`-module are exactly the minimal
primes above `(f)` in a unique factorization ring. Unlike a classification by
prime factors, this also includes the case `f = 0`. Mathlib's associated primes
are defined using radicals of annihilators, rather than requiring an exact
prime annihilator. Vakil's Exercise 6.6.F motivates the principal-quotient case;
the comparison uses Mathlib's associated-prime API and the existing principal-
ideal classification in `MinimalPrimes.Principal`. -/
theorem associatedPrimes_quotient_span_singleton_eq_minimalPrimes
    {R : Type u} [CommRing R] [UniqueFactorizationMonoid R] (f : R) :
    associatedPrimes R (R ⧸ Ideal.span {f}) = (Ideal.span {f}).minimalPrimes := by
  by_cases hTrivial : Subsingleton R
  · let : Subsingleton R := hTrivial
    have hTop : span {f} = (⊤ : Ideal R) := by
      rw [show f = 1 from Subsingleton.elim f 1]
      simp
    rw [associatedPrimes.eq_empty_of_subsingleton, hTop, minimalPrimes_top]
  · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hTrivial
    let : IsDomain R := {}
    by_cases hZero : f = 0
    · subst f
      have hPrime : (span {(0 : R)} : Ideal R).IsPrime := by
        simpa using (inferInstance : (⊥ : Ideal R).IsPrime)
      have hAssociated : associatedPrimes R (R ⧸ span {(0 : R)}) =
          {span {(0 : R)}} := by
        ext primeIdeal
        constructor
        · intro hMem
          exact (IsAssociatedPrime.eq_radical hPrime.isPrimary hMem).trans hPrime.radical
        · intro hMem
          have hEqual : primeIdeal = span {(0 : R)} := Set.mem_singleton_iff.mp hMem
          subst primeIdeal
          have hColon := colon_mk_mul_eq (0 : R) (1 : R) one_ne_zero
          rw [mul_one] at hColon
          exact ⟨hPrime, ⟨Ideal.Quotient.mk (span {(0 : R)}) 1,
            by rw [hColon, hPrime.radical]⟩⟩
      exact hAssociated.trans minimalPrimes_eq_subsingleton_self.symm
    · exact associatedPrimes_quotient_span_singleton_eq_minimalPrimes_of_ne_zero f hZero

end Ideal
