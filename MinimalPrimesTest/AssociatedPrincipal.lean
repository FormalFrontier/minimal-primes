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
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Principal-quotient associated-prime examples

The zero and unit generators give opposite boundary cases. In `ℤ/12ℤ`,
the classes of `6` and `4` have exact annihilators `(2)` and `(3)`;
the corresponding quotient-spectrum points have distinct exact quotient-ring
annihilators. These calculations are independent of the principal-quotient
comparison.
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

private abbrev twelveIdeal : Ideal ℤ := Ideal.span {(12 : ℤ)}

private theorem twelve_le_two : twelveIdeal ≤ Ideal.span {(2 : ℤ)} := by
  rw [Ideal.span_singleton_le_span_singleton]
  norm_num

private theorem twelve_le_three : twelveIdeal ≤ Ideal.span {(3 : ℤ)} := by
  rw [Ideal.span_singleton_le_span_singleton]
  norm_num

private noncomputable def twoQuotientPoint : PrimeSpectrum (ℤ ⧸ twelveIdeal) := by
  haveI : (Ideal.span {(2 : ℤ)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime Int.prime_two
  exact ⟨(Ideal.span {(2 : ℤ)}).map (Ideal.Quotient.mk twelveIdeal),
    Ideal.isPrime_map_quotientMk_of_isPrime twelve_le_two⟩

private noncomputable def threeQuotientPoint : PrimeSpectrum (ℤ ⧸ twelveIdeal) := by
  haveI : (Ideal.span {(3 : ℤ)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime Int.prime_three
  exact ⟨(Ideal.span {(3 : ℤ)}).map (Ideal.Quotient.mk twelveIdeal),
    Ideal.isPrime_map_quotientMk_of_isPrime twelve_le_three⟩

private theorem two_point_image :
    ((twelveIdeal.primeSpectrumQuotientOrderIsoZeroLocus twoQuotientPoint).1).asIdeal =
      Ideal.span {(2 : ℤ)} := by
  change ((Ideal.span {(2 : ℤ)}).map (Ideal.Quotient.mk twelveIdeal)).comap
    (Ideal.Quotient.mk twelveIdeal) = Ideal.span {(2 : ℤ)}
  exact Ideal.comap_map_mk twelve_le_two

private theorem three_point_image :
    ((twelveIdeal.primeSpectrumQuotientOrderIsoZeroLocus threeQuotientPoint).1).asIdeal =
      Ideal.span {(3 : ℤ)} := by
  change ((Ideal.span {(3 : ℤ)}).map (Ideal.Quotient.mk twelveIdeal)).comap
    (Ideal.Quotient.mk twelveIdeal) = Ideal.span {(3 : ℤ)}
  exact Ideal.comap_map_mk twelve_le_three

private theorem two_and_three_quotient_points_distinct :
    twoQuotientPoint ≠ threeQuotientPoint := by
  intro hEqual
  have hImageEqual := congrArg
    (fun point : PrimeSpectrum (ℤ ⧸ twelveIdeal) =>
      ((twelveIdeal.primeSpectrumQuotientOrderIsoZeroLocus point).1).asIdeal) hEqual
  rw [two_point_image, three_point_image] at hImageEqual
  have hDivides : (3 : ℤ) ∣ (2 : ℤ) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hImageEqual]
    exact Ideal.mem_span_singleton_self (2 : ℤ)
  norm_num at hDivides

private theorem two_point_exact_annihilator :
    twoQuotientPoint.asIdeal =
      (⊥ : Submodule (ℤ ⧸ twelveIdeal) (ℤ ⧸ twelveIdeal)).colon
        {Ideal.Quotient.mk twelveIdeal (6 : ℤ)} := by
  apply (Ideal.comap_injective_of_surjective
    (Ideal.Quotient.mk twelveIdeal) Ideal.Quotient.mk_surjective)
  rw [← Ideal.Quotient.algebraMap_eq twelveIdeal]
  rw [← Submodule.colon_restrictScalars (R := ℤ), Submodule.restrictScalars_bot,
    Ideal.Quotient.algebraMap_eq twelveIdeal, annihilator_six_mod_twelve]
  exact two_point_image

private theorem three_point_exact_annihilator :
    threeQuotientPoint.asIdeal =
      (⊥ : Submodule (ℤ ⧸ twelveIdeal) (ℤ ⧸ twelveIdeal)).colon
        {Ideal.Quotient.mk twelveIdeal (4 : ℤ)} := by
  apply (Ideal.comap_injective_of_surjective
    (Ideal.Quotient.mk twelveIdeal) Ideal.Quotient.mk_surjective)
  rw [← Ideal.Quotient.algebraMap_eq twelveIdeal]
  rw [← Submodule.colon_restrictScalars (R := ℤ), Submodule.restrictScalars_bot,
    Ideal.Quotient.algebraMap_eq twelveIdeal, annihilator_four_mod_twelve]
  exact three_point_image

private theorem two_point_associated_from_minimal_primes :
    twoQuotientPoint.asIdeal ∈ associatedPrimes (ℤ ⧸ twelveIdeal) (ℤ ⧸ twelveIdeal) := by
  apply (Ideal.isAssociatedPrime_quotient_iff_minimalPrimes (12 : ℤ) twoQuotientPoint).2
  rw [two_point_image]
  exact two_and_three_minimal_over_twelve.1

private theorem two_point_associated_from_scalar_contraction :
    IsAssociatedPrime twoQuotientPoint.asIdeal (ℤ ⧸ twelveIdeal) := by
  apply (IsAssociatedPrime.comap_algebraMap_iff (R := ℤ)
    (M := ℤ ⧸ twelveIdeal) twoQuotientPoint.asIdeal
    (by simpa only [Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk twelveIdeal)))).1
  have hImage : twoQuotientPoint.asIdeal.comap
      (algebraMap ℤ (ℤ ⧸ twelveIdeal)) = Ideal.span {(2 : ℤ)} := by
    change ((twelveIdeal.primeSpectrumQuotientOrderIsoZeroLocus twoQuotientPoint).1).asIdeal =
      Ideal.span {(2 : ℤ)}
    exact two_point_image
  rw [hImage]
  exact associated_two_and_three_mod_twelve.1

private theorem two_point_exact_from_minimal_primes :
    ∃ witness : ℤ ⧸ twelveIdeal, twoQuotientPoint.asIdeal =
      (⊥ : Submodule (ℤ ⧸ twelveIdeal) (ℤ ⧸ twelveIdeal)).colon {witness} := by
  apply (Ideal.exists_colon_quotient_iff_minimalPrimes (12 : ℤ) twoQuotientPoint).2
  rw [two_point_image]
  exact two_and_three_minimal_over_twelve.1

private theorem zero_quotient_point_image :
    ∃ x : PrimeSpectrum (ℤ ⧸ Ideal.span {(0 : ℤ)}),
      ((Ideal.span {(0 : ℤ)}).primeSpectrumQuotientOrderIsoZeroLocus x).1.asIdeal =
        (⊥ : Ideal ℤ) := by
  have hZero : Ideal.span {(0 : ℤ)} ≤ (⊥ : Ideal ℤ) := by simp
  let x : PrimeSpectrum (ℤ ⧸ Ideal.span {(0 : ℤ)}) :=
    ⟨(⊥ : Ideal ℤ).map (Ideal.Quotient.mk (Ideal.span {(0 : ℤ)})),
      Ideal.isPrime_map_quotientMk_of_isPrime hZero⟩
  refine ⟨x, ?_⟩
  change ((⊥ : Ideal ℤ).map (Ideal.Quotient.mk (Ideal.span {(0 : ℤ)}))).comap
    (Ideal.Quotient.mk (Ideal.span {(0 : ℤ)})) = ⊥
  exact Ideal.comap_map_mk hZero

private theorem zero_quotient_annihilator_one :
    (⊥ : Submodule ℤ (ℤ ⧸ Ideal.span {(0 : ℤ)})).colon
      {Ideal.Quotient.mk (Ideal.span {(0 : ℤ)}) (1 : ℤ)} = ⊥ := by
  simpa using (Ideal.colon_quotient_mk_mul_eq_span_singleton
    (0 : ℤ) (1 : ℤ) one_ne_zero)

private theorem unit_quotient_spectrum_empty :
    IsEmpty (PrimeSpectrum (ℤ ⧸ Ideal.span {(1 : ℤ)})) := by
  have hTop : Ideal.span {(1 : ℤ)} = (⊤ : Ideal ℤ) := by simp
  rw [hTop]
  infer_instance

private theorem subsingleton_quotient_spectrum_empty :
    IsEmpty (PrimeSpectrum (ZMod 1 ⧸ Ideal.span {(0 : ZMod 1)})) := by
  infer_instance

end MinimalPrimesTest
