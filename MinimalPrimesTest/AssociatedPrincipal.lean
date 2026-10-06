/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.AssociatedPrincipal
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal-quotient associated-prime examples

The zero and unit generators give opposite boundary cases. In `ℤ/12ℤ`,
the classes of `6` and `4` have exact annihilators `(2)` and `(3)`;
these calculations are independent of the principal-quotient comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

@[expose] public section

namespace MinimalPrimesTest

/-- In `ℤ/12ℤ`, the class of `6` has exact annihilator `(2)`, exhibiting one
associated prime despite the repeated factor of `2` in `12`. -/
theorem annihilator_six_mod_twelve :
    (⊥ : Submodule ℤ (ℤ ⧸ Ideal.span {(12 : ℤ)})).colon
      {Ideal.Quotient.mk (Ideal.span {(12 : ℤ)}) (6 : ℤ)} =
      Ideal.span {(2 : ℤ)} := by
  ext r
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  rw [show (12 : ℤ) = 2 * 6 by norm_num,
    mul_dvd_mul_iff_right (by norm_num : (6 : ℤ) ≠ 0)]
  exact Ideal.mem_span_singleton.symm

private theorem annihilator_four_mod_twelve :
    (⊥ : Submodule ℤ (ℤ ⧸ Ideal.span {(12 : ℤ)})).colon
      {Ideal.Quotient.mk (Ideal.span {(12 : ℤ)}) (4 : ℤ)} =
      Ideal.span {(3 : ℤ)} := by
  ext r
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  rw [show (12 : ℤ) = 3 * 4 by norm_num,
    mul_dvd_mul_iff_right (by norm_num : (4 : ℤ) ≠ 0)]
  exact Ideal.mem_span_singleton.symm

private theorem associated_two_and_three_mod_twelve :
    Ideal.span {(2 : ℤ)} ∈ associatedPrimes ℤ (ℤ ⧸ Ideal.span {(12 : ℤ)}) ∧
      Ideal.span {(3 : ℤ)} ∈ associatedPrimes ℤ (ℤ ⧸ Ideal.span {(12 : ℤ)}) := by
  constructor
  · exact ⟨Ideal.isPrime_span_singleton_of_prime Int.prime_two,
      ⟨Ideal.Quotient.mk (Ideal.span {(12 : ℤ)}) (6 : ℤ), by
        rw [annihilator_six_mod_twelve]
        exact (Ideal.isPrime_span_singleton_of_prime Int.prime_two).radical.symm⟩⟩
  · exact ⟨Ideal.isPrime_span_singleton_of_prime Int.prime_three,
      ⟨Ideal.Quotient.mk (Ideal.span {(12 : ℤ)}) (4 : ℤ), by
        rw [annihilator_four_mod_twelve]
        exact (Ideal.isPrime_span_singleton_of_prime Int.prime_three).radical.symm⟩⟩

private theorem two_and_three_minimal_over_twelve :
    Ideal.span {(2 : ℤ)} ∈ (Ideal.span {(12 : ℤ)}).minimalPrimes ∧
      Ideal.span {(3 : ℤ)} ∈ (Ideal.span {(12 : ℤ)}).minimalPrimes := by
  rw [← Ideal.associatedPrimes_quotient_span_singleton_eq_minimalPrimes (12 : ℤ)]
  exact associated_two_and_three_mod_twelve

private theorem associated_primes_unit_quotient_empty :
    associatedPrimes ℤ (ℤ ⧸ Ideal.span {(1 : ℤ)}) = ∅ := by
  rw [show Ideal.span {(1 : ℤ)} = (⊤ : Ideal ℤ) by simp]
  exact associatedPrimes.eq_empty_of_subsingleton

private theorem minimal_primes_unit_ideal_empty :
    (Ideal.span {(1 : ℤ)}).minimalPrimes = ∅ := by
  simpa using (Ideal.minimalPrimes_top (R := ℤ))

private theorem minimal_primes_zero_ideal_contains_zero :
    (⊥ : Ideal ℤ) ∈ (Ideal.span {(0 : ℤ)}).minimalPrimes := by
  rw [show Ideal.span {(0 : ℤ)} = (⊥ : Ideal ℤ) by simp,
    Ideal.minimalPrimes_eq_subsingleton_self]
  simp

private theorem associated_primes_zero_quotient_contains_zero :
    (⊥ : Ideal ℤ) ∈ associatedPrimes ℤ (ℤ ⧸ Ideal.span {(0 : ℤ)}) := by
  have hcolon :
      (⊥ : Submodule ℤ (ℤ ⧸ Ideal.span {(0 : ℤ)})).colon
        {(1 : ℤ ⧸ Ideal.span {(0 : ℤ)})} = ⊥ := by
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change r • (1 : ℤ ⧸ Ideal.span {(0 : ℤ)}) = 0 ↔ r ∈ (⊥ : Ideal ℤ)
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    simp
  exact ⟨inferInstance, ⟨1, by rw [hcolon, (inferInstance : (⊥ : Ideal ℤ).IsPrime).radical]⟩⟩

private theorem trivial_ring_ufm_and_quotient_boundary :
    UniqueFactorizationMonoid (ZMod 1) ∧
    associatedPrimes (ZMod 1) (ZMod 1 ⧸ Ideal.span {(0 : ZMod 1)}) =
      (Ideal.span {(0 : ZMod 1)}).minimalPrimes := by
  refine ⟨UniqueFactorizationMonoid.of_subsingleton (ZMod 1), ?_⟩
  rw [associatedPrimes.eq_empty_of_subsingleton]
  have htop : Ideal.span {(0 : ZMod 1)} = ⊤ := by
    rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _]
    simp
  rw [htop, Ideal.minimalPrimes_top]

end MinimalPrimesTest
