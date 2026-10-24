/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization
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

namespace Localization.AtPrime

/-- In the localization of the integers at `(2)`, the radical of the extension of `(4)`
is the extension of `(2)`, whereas the radical of the extended unit ideal is not. -/
theorem integer_four_at_two
    [h2 : (Ideal.span {(2 : ℤ)} : Ideal ℤ).IsPrime] :
    ((Ideal.span {(4 : ℤ)}).map
      (algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)})))).radical =
      (Ideal.span {(2 : ℤ)}).map
        (algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)}))) ∧
    ((⊤ : Ideal ℤ).map
      (algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)})))).radical ≠
      (Ideal.span {(2 : ℤ)}).map
        (algebraMap ℤ (Localization.AtPrime (Ideal.span {(2 : ℤ)}))) := by
  constructor
  · apply (IsLocalization.AtPrime.radical_map_eq_iff_mem_minimalPrimes
      (A := Localization.AtPrime (span {(2 : ℤ)})) (span {(2 : ℤ)}) (span {(4 : ℤ)})).mpr
    have hfour : span {(4 : ℤ)} = span {(2 : ℤ)} ^ 2 := by
      rw [Ideal.span_singleton_pow]
      rfl
    have hrad : (span {(4 : ℤ)}).radical = span {(2 : ℤ)} := by
      rw [hfour, Ideal.radical_pow _ two_ne_zero]
      exact Ideal.IsPrime.radical inferInstance
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · intro h
    have hm := IsLocalization.AtPrime.mem_minimalPrimes_of_radical_map_eq
      (A := Localization.AtPrime (span {(2 : ℤ)})) (span {(2 : ℤ)}) ⊤ h
    rw [Ideal.minimalPrimes_top] at hm
    exact Set.notMem_empty _ hm

end Localization.AtPrime
