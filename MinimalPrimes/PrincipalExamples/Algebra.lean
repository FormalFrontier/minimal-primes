/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Principal
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.NormNum

/-!
# Minimal primes of the integer twelve

The repeated factor two occurs twice in the normalized factor multiset, but
contributes only one minimal prime. All integer calculations use the exported
positive-representative normalization. This algebraic module does not depend on
irreducible components or the aggregate import.

## References

The proofs use Mathlib's normalized-factor and integer-normalization APIs and
the factor-to-minimal-prime equivalence in `MinimalPrimes.Principal`.
-/

noncomputable section

open UniqueFactorizationMonoid

namespace MinimalPrimes.PrincipalExamples

universe u

private theorem prime_square_factor_boundary
    (R : Type u) [CommRing R] [UniqueFactorizationMonoid R]
    [StrongNormalizationMonoid R] (p : R) (hp : Prime p)
    (hSquare : p ^ 2 ≠ 0) :
    normalizedFactors (p ^ 2) =
      Multiset.cons (normalize p) (Multiset.cons (normalize p) 0) ∧
    (Ideal.span {p ^ 2}).minimalPrimes = {Ideal.span {p}} ∧
    ∃ hN : normalize p ∈ normalizedFactors (p ^ 2),
      (Ideal.normalizedFactorsEquivMinimalPrimes hSquare
        ⟨normalize p, hN⟩).1 = Ideal.span {p} := by
  classical
  have hpI : Irreducible p := hp.irreducible
  have hF : normalizedFactors (p ^ 2) =
      Multiset.cons (normalize p) (Multiset.cons (normalize p) 0) := by
    simpa using hpI.normalizedFactors_pow 2
  have hN : normalize p ∈ normalizedFactors (p ^ 2) := by
    simp [hF]
  have hFp : normalizedFactors p = {normalize p} :=
    normalizedFactors_irreducible hpI
  have hAssoc : Associated (normalize p) p := by
    simpa only [hFp, Multiset.prod_singleton] using
      (prod_normalizedFactors hpI.ne_zero)
  have hspan : (Ideal.span {normalize p} : Ideal R) = Ideal.span {p} := by
    apply le_antisymm
    · exact (Ideal.span_singleton_le_iff_mem
        (I := Ideal.span {p})).mpr
        ((Ideal.mem_iff_of_associated hAssoc).mpr
          (Ideal.mem_span_singleton_self p))
    · exact (Ideal.span_singleton_le_iff_mem
        (I := Ideal.span {normalize p})).mpr
        ((Ideal.mem_iff_of_associated hAssoc).mp
          (Ideal.mem_span_singleton_self (normalize p)))
  have hM : (Ideal.span {p ^ 2}).minimalPrimes = {Ideal.span {p}} := by
    rw [Ideal.minimalPrimes_span_singleton_eq_normalizedFactors hSquare]
    ext Q
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqN : q = normalize p := by simpa [hF] using hq
      simp [hqN, hspan]
    · intro hQ
      have hQp : Q = Ideal.span {p} := by simpa using hQ
      exact ⟨normalize p, hN, hQp.trans hspan.symm⟩
  refine ⟨hF, hM, hN, ?_⟩
  exact (Ideal.normalizedFactorsEquivMinimalPrimes_apply hSquare
    ⟨normalize p, hN⟩).trans hspan

private theorem integer_twelve_factors :
    normalizedFactors (12 : ℤ) =
      Multiset.cons 2 (Multiset.cons 2 (Multiset.cons 3 0)) := by
  have hp2 : Prime (2 : ℤ) := Int.prime_two
  have hp3 : Prime (3 : ℤ) := Int.prime_three
  have hSquare := prime_square_factor_boundary ℤ (2 : ℤ) hp2
    (by norm_num : (2 : ℤ) ^ 2 ≠ 0)
  have hmul := normalizedFactors_mul
    (by norm_num : (2 : ℤ) ^ 2 ≠ 0) (by norm_num : (3 : ℤ) ≠ 0)
  rw [Multiset.cons_zero]
  simpa only [show (2 : ℤ) ^ 2 * 3 = 12 by norm_num,
    hSquare.1,
    normalizedFactors_irreducible hp3.irreducible,
    Int.normalize_of_nonneg (by norm_num : 0 ≤ (2 : ℤ)),
    Int.normalize_of_nonneg (by norm_num : 0 ≤ (3 : ℤ)),
    Multiset.cons_add, zero_add] using hmul

/-- Twelve has normalized factors two, two, and three, and exactly the two
minimal primes `(2)` and `(3)`. The factor-to-minimal-prime equivalence sends
the two distinct factor values to those ideals. -/
public theorem integer_twelve_factor_algebra (h12 : (12 : ℤ) ≠ 0) :
    normalizedFactors (12 : ℤ) =
      Multiset.cons 2 (Multiset.cons 2 (Multiset.cons 3 0)) ∧
    (Ideal.span {(12 : ℤ)}).minimalPrimes =
      {Ideal.span {(2 : ℤ)}, Ideal.span {(3 : ℤ)}} ∧
    (Ideal.span {(2 : ℤ)} : Ideal ℤ) ≠ Ideal.span {(3 : ℤ)} ∧
    ∃ (h2 : (2 : ℤ) ∈ normalizedFactors (12 : ℤ))
      (h3 : (3 : ℤ) ∈ normalizedFactors (12 : ℤ)),
      (Ideal.normalizedFactorsEquivMinimalPrimes h12 ⟨2, h2⟩).1 =
        Ideal.span {(2 : ℤ)} ∧
      (Ideal.normalizedFactorsEquivMinimalPrimes h12 ⟨3, h3⟩).1 =
        Ideal.span {(3 : ℤ)} := by
  have hF := integer_twelve_factors
  have h2 : (2 : ℤ) ∈ normalizedFactors (12 : ℤ) := by simp [hF]
  have h3 : (3 : ℤ) ∈ normalizedFactors (12 : ℤ) := by simp [hF]
  have hM : (Ideal.span {(12 : ℤ)}).minimalPrimes =
      {Ideal.span {(2 : ℤ)}, Ideal.span {(3 : ℤ)}} := by
    rw [Ideal.minimalPrimes_span_singleton_eq_normalizedFactors h12]
    ext P
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' : p = 2 ∨ p = 3 := by simpa [hF, or_assoc] using hp
      rcases hp' with rfl | rfl <;> simp
    · intro hp
      have hp' : P = Ideal.span {(2 : ℤ)} ∨ P = Ideal.span {(3 : ℤ)} := by
        simpa using hp
      rcases hp' with rfl | rfl
      · exact ⟨2, h2, rfl⟩
      · exact ⟨3, h3, rfl⟩
  have hD : (Ideal.span {(2 : ℤ)} : Ideal ℤ) ≠ Ideal.span {(3 : ℤ)} := by
    intro h
    have he : Ideal.normalizedFactorsEquivMinimalPrimes h12 ⟨2, h2⟩ =
        Ideal.normalizedFactorsEquivMinimalPrimes h12 ⟨3, h3⟩ := by
      apply Subtype.ext
      simpa only [Ideal.normalizedFactorsEquivMinimalPrimes_apply] using h
    have hv := congrArg Subtype.val
      ((Ideal.normalizedFactorsEquivMinimalPrimes h12).injective he)
    norm_num at hv
  exact ⟨hF, hM, hD, h2, h3,
    Ideal.normalizedFactorsEquivMinimalPrimes_apply h12 ⟨2, h2⟩,
    Ideal.normalizedFactorsEquivMinimalPrimes_apply h12 ⟨3, h3⟩⟩

end MinimalPrimes.PrincipalExamples
