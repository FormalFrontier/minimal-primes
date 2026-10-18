/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization
import Mathlib.Data.Nat.Prime.Int

/-!
# Integer localization at the prime ideal `(2)`

The localization of `(4)` has radical equal to the extension of `(2)`. The proof
uses the localized-radical criterion after computing the minimal prime using Mathlib's
radical-of-a-power and principal-ideal power lemmas. The unit ideal supplies a boundary
case: its localized radical cannot be the extension of `(2)`.
-/

@[expose] public section

open Ideal

private instance : (span {(2 : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime Int.prime_two

private theorem integer_four_localized_radical :
    ((span {(4 : ℤ)}).map
      (algebraMap ℤ (Localization.AtPrime (span {(2 : ℤ)})))).radical =
    (span {(2 : ℤ)}).map
      (algebraMap ℤ (Localization.AtPrime (span {(2 : ℤ)}))) := by
  apply (IsLocalization.AtPrime.radical_map_eq_iff_mem_minimalPrimes
    (A := Localization.AtPrime (span {(2 : ℤ)})) (span {(2 : ℤ)}) (span {(4 : ℤ)})).mpr
  have hfour : span {(4 : ℤ)} = span {(2 : ℤ)} ^ 2 := by
    rw [Ideal.span_singleton_pow]
    rfl
  have hrad : (span {(4 : ℤ)}).radical = span {(2 : ℤ)} := by
    rw [hfour, Ideal.radical_pow _ two_ne_zero]
    exact Ideal.IsPrime.radical inferInstance
  rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

private theorem integer_top_localized_radical_ne :
    ((⊤ : Ideal ℤ).map
      (algebraMap ℤ (Localization.AtPrime (span {(2 : ℤ)})))).radical ≠
    (span {(2 : ℤ)}).map
      (algebraMap ℤ (Localization.AtPrime (span {(2 : ℤ)}))) := by
  intro h
  have hm := IsLocalization.AtPrime.mem_minimalPrimes_of_radical_map_eq
    (A := Localization.AtPrime (span {(2 : ℤ)})) (span {(2 : ℤ)}) ⊤ h
  rw [Ideal.minimalPrimes_top] at hm
  exact Set.notMem_empty _ hm
