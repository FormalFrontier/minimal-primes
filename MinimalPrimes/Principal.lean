/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Principal prime ideals and minimal primes in semirings with unique factorization

This file classifies the minimal primes over a nonzero principal ideal in a
commutative semiring with unique factorization. The classification uses membership in
the multiset of normalized factors, and therefore deliberately forgets factor
multiplicity. The caller supplies a `NormalizationMonoid` instance, so the factors
in the results use the caller's chosen normalized representatives. The classification results
assume the element is nonzero; units have no factors or minimal primes above
their principal ideal.

Independently of normalization, every nonunit belongs to a principal prime ideal.
This includes zero, whose witness is bottom. Any proper principal ideal avoids at
least one of two relatively prime elements; this avoidance does not require unique
factorization or primeness. Contracting a target witness along a homomorphism from
an arbitrary semiring gives a prime two-sided source ideal, not necessarily a
principal ideal. Avoidance is disjunctive, not simultaneous.

## References

* Mathlib's minimal-prime and normalized-factor APIs provide the underlying
  definitions and factorization results.
* The witness constructions use Mathlib's principal-generator, irreducible-factor,
  singleton-span, prime-bottom, and ideal-comap APIs.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 3.7.H, provides the ring-theoretic motivation. The
  classification here also applies to commutative semirings.
-/

@[expose] public section

noncomputable section

open UniqueFactorizationMonoid

universe u v

namespace Ideal

section PrincipalPrimeWitness

section CommSemiring

variable {A : Type u} {B : Type v} [Semiring A] [CommSemiring B]

/-- A proper principal ideal cannot contain both of two relatively prime elements.
This statement does not require unique factorization or primality of the ideal. -/
theorem not_mem_or_not_mem_of_isPrincipal_of_isRelPrime
    (Q : Ideal B) [Q.IsPrincipal] (hQ : Q ≠ ⊤) {a b : B}
    (hab : IsRelPrime a b) : a ∉ Q ∨ b ∉ Q := by
  classical
  by_cases ha : a ∈ Q
  · right
    intro hb
    have hunit : IsUnit (Submodule.IsPrincipal.generator Q) := hab
      ((Submodule.IsPrincipal.mem_iff_generator_dvd Q).mp ha)
      ((Submodule.IsPrincipal.mem_iff_generator_dvd Q).mp hb)
    apply hQ
    rw [← Ideal.span_singleton_generator Q]
    exact Ideal.span_singleton_eq_top.mpr hunit
  · exact Or.inl ha

variable [UniqueFactorizationMonoid B]

/-- Every nonunit belongs to some principal prime ideal, including when the nonunit is zero.
No explicit domain, nontriviality, normalization, or nonzero hypothesis is imposed. -/
theorem exists_mem_principal_prime_of_not_isUnit {r : B} (hr : ¬ IsUnit r) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.IsPrincipal ∧ r ∈ Q := by
  classical
  -- A nonunit distinguishes the semiring from the subsingleton case.
  let : Nontrivial B := ⟨⟨r, 1, by
    intro h
    apply hr
    rw [h]
    exact isUnit_one⟩⟩
  by_cases hr0 : r = 0
  · refine ⟨⊥, inferInstance, inferInstance, ?_⟩
    simpa only [hr0] using (Ideal.zero_mem (⊥ : Ideal B))
  · obtain ⟨p, hp, hpr⟩ := WfDvdMonoid.exists_irreducible_factor hr hr0
    exact ⟨Ideal.span {p}, Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp), inferInstance,
      Ideal.mem_span_singleton.mpr hpr⟩

/-- A principal prime ideal containing a nonunit avoids at least one of two relatively prime
 elements. The avoidance is disjunctive, not simultaneous. -/
theorem exists_mem_principal_prime_of_isRelPrime {a b r : B}
    (hab : IsRelPrime a b) (hr : ¬ IsUnit r) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.IsPrincipal ∧ r ∈ Q ∧ (a ∉ Q ∨ b ∉ Q) := by
  obtain ⟨Q, hprime, hprincipal, hrQ⟩ := exists_mem_principal_prime_of_not_isUnit hr
  let : Q.IsPrincipal := hprincipal
  exact ⟨Q, hprime, hprincipal, hrQ,
    not_mem_or_not_mem_of_isPrincipal_of_isRelPrime Q hprime.ne_top hab⟩

end CommSemiring

/-- Contract a principal prime target witness along an arbitrary unital semiring homomorphism.
The source witness is the displayed `Q.comap φ`, a completely prime two-sided ideal, not an
unspecified left-prime ideal. No source principality, maximality, domain, injectivity, nonzero,
or simultaneous-avoidance assertion is made. -/
theorem exists_comap_principal_prime_of_isRelPrime
    {A : Type u} {B : Type v} [Semiring A] [CommSemiring B]
    [UniqueFactorizationMonoid B] (φ : A →+* B) {a b r : A}
    (hab : IsRelPrime (φ a) (φ b)) (hr : ¬ IsUnit (φ r)) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.IsPrincipal ∧
      (Q.comap φ).IsPrime ∧ (Q.comap φ).IsTwoSided ∧
      r ∈ Q.comap φ ∧ (a ∉ Q.comap φ ∨ b ∉ Q.comap φ) := by
  obtain ⟨Q, hprime, hprincipal, hrQ, havoid⟩ :=
    exists_mem_principal_prime_of_isRelPrime hab hr
  let : Q.IsPrime := hprime
  refine ⟨Q, hprime, hprincipal, inferInstance, inferInstance, ?_, ?_⟩
  · exact Ideal.mem_comap.mpr hrQ
  · simpa only [Ideal.mem_comap] using havoid

end PrincipalPrimeWitness

variable {R : Type u} [CommSemiring R] [UniqueFactorizationMonoid R]
  [NormalizationMonoid R]

/-- The minimal primes over a nonzero principal ideal in a commutative semiring
with unique factorization are the principal ideals generated by the normalized
irreducible factors.

Membership in `normalizedFactors f` is a proposition about a multiset, so this
set equality intentionally forgets the multiplicity of repeated factors.
The proof factors `f` up to association, uses primality to select a factor of
the product, and uses minimality in both directions. The nonzero assumption
excludes zero, whose empty factor multiset does not classify `(0)`. -/
theorem minimalPrimes_span_singleton_eq_normalizedFactors {f : R} (hf : f ≠ 0) :
    (span {f}).minimalPrimes =
      {P | ∃ p ∈ normalizedFactors f, P = span {p}} := by
  ext P
  constructor
  · intro hP
    have hfP : f ∈ P := hP.le (mem_span_singleton_self f)
    have hprodP : (normalizedFactors f).prod ∈ P :=
      (mem_iff_of_associated
        (UniqueFactorizationMonoid.prod_normalizedFactors hf)).mpr hfP
    obtain ⟨p, hpf, hpP⟩ :=
      hP.isPrime.multiset_prod_mem_iff_exists_mem (normalizedFactors f) |>.mp hprodP
    have hpPrime : (span {p} : Ideal R).IsPrime :=
      isPrime_span_singleton_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor p hpf)
    have hfspan : span {f} ≤ span {p} := by
      rw [span_singleton_le_iff_mem, mem_span_singleton]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpf
    have hspanP : span {p} ≤ P :=
      (span_singleton_le_iff_mem (I := P)).mpr hpP
    exact ⟨p, hpf, le_antisymm (hP.2 ⟨hpPrime, hfspan⟩ hspanP) hspanP⟩
  · rintro ⟨p, hpf, rfl⟩
    have hpPrime : (span {p} : Ideal R).IsPrime :=
      isPrime_span_singleton_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor p hpf)
    have hfspan : span {f} ≤ span {p} := by
      rw [span_singleton_le_iff_mem, mem_span_singleton]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpf
    refine ⟨⟨hpPrime, hfspan⟩, ?_⟩
    intro Q hQ hQle
    have hfQ : f ∈ Q := hQ.2 (mem_span_singleton_self f)
    have hprodQ : (normalizedFactors f).prod ∈ Q :=
      (mem_iff_of_associated
        (UniqueFactorizationMonoid.prod_normalizedFactors hf)).mpr hfQ
    obtain ⟨q, hqf, hqQ⟩ :=
      hQ.1.multiset_prod_mem_iff_exists_mem (normalizedFactors f) |>.mp hprodQ
    have hspanqQ : span {q} ≤ Q :=
      (span_singleton_le_iff_mem (I := Q)).mpr hqQ
    have hp_dvd_q : p ∣ q := mem_span_singleton.mp <|
      hQle (hspanqQ (mem_span_singleton_self q))
    have hpq : p = q :=
      UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd f p hpf q hqf hp_dvd_q
    simpa [hpq] using hspanqQ

/-- The normalized factor *values* of a nonzero element are equivalent to the
minimal primes over its principal ideal. The forward map sends a factor to its
principal ideal; `Equiv.ofBijective` selects the inverse noncomputably. Repeated
occurrences of a factor are not separate elements of the subtype. -/
def normalizedFactorsEquivMinimalPrimes {f : R} (hf : f ≠ 0) :
    {p // p ∈ normalizedFactors f} ≃ (span {f}).minimalPrimes := by
  exact Equiv.ofBijective
    (fun p ↦ ⟨span {p.1}, by
      rw [minimalPrimes_span_singleton_eq_normalizedFactors hf]
      exact ⟨p.1, p.2, rfl⟩⟩)
    ⟨by
      intro p q hpq
      apply Subtype.ext
      apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated p.2 q.2
      have hspan : span {p.1} = span {q.1} := congrArg Subtype.val hpq
      apply dvd_dvd_iff_associated.mp
      constructor
      · apply mem_span_singleton.mp
        rw [hspan]
        exact mem_span_singleton_self q.1
      · apply mem_span_singleton.mp
        rw [← hspan]
        exact mem_span_singleton_self p.1,
    by
      intro P
      have hP : ∃ p ∈ normalizedFactors f, P.1 = span {p} := by
        have hm := congrArg (fun s : Set (Ideal R) ↦ P.1 ∈ s)
          (minimalPrimes_span_singleton_eq_normalizedFactors hf)
        exact (Iff.of_eq hm).mp P.2
      obtain ⟨p, hpf, hpP⟩ := hP
      refine ⟨⟨p, hpf⟩, ?_⟩
      apply Subtype.ext
      exact hpP.symm⟩

/-- The factor-to-minimal-prime equivalence sends a normalized factor to its
principal ideal. This forward-map equality holds by `rfl` and is a simp lemma. -/
@[simp]
theorem normalizedFactorsEquivMinimalPrimes_apply {f : R} (hf : f ≠ 0)
    (p : {p // p ∈ normalizedFactors f}) :
    (normalizedFactorsEquivMinimalPrimes hf p).1 = span {p.1} :=
  rfl

end Ideal
