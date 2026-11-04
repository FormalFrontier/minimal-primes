/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.MinimalPrimeLocalization
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.NormNum

/-!
# Localized radicals over the integers and natural numbers

Over the integers, the localization of `(4)` has radical equal to the extension of `(2)`.
The proof uses the localized-radical criterion after computing the minimal prime using
Mathlib's radical-of-a-power and principal-ideal power lemmas. The unit ideal supplies a
boundary case: its localized radical cannot be the extension of `(2)`.

Over the natural numbers, `2` lies in the radical of `(4)` but not in `(4)` itself, and
passes all the minimal-prime localization tests. In contrast, `1` fails those tests for
the same ideal. For the unit ideal of any commutative semiring, all elements pass.
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

/-- In `ℕ`, `2` is not in `(4)` but passes every minimal-prime localization test for `(4)`,
since its square belongs to `(4)`. -/
private theorem nat_four_two_localizations :
    (2 : ℕ) ∉ Ideal.span {(4 : ℕ)} ∧
      ∀ (q : Ideal ℕ) [q.IsPrime], q ∈ (Ideal.span {(4 : ℕ)}).minimalPrimes →
        algebraMap ℕ (Localization.AtPrime q) 2 ∈
          (Ideal.map (algebraMap ℕ (Localization.AtPrime q)) (Ideal.span {(4 : ℕ)})).radical := by
  refine ⟨by norm_num [Ideal.mem_span_singleton], ?_⟩
  apply (Ideal.mem_radical_iff_forall_minimalPrimes_localization (Ideal.span {(4 : ℕ)}) 2).mp
  exact ⟨2, by norm_num [Ideal.mem_span_singleton]⟩

/-- In `ℕ`, `1` fails the localization tests for `(4)`, so the family being tested is
nonempty and the tests are not true for every element. -/
private theorem nat_four_one_not_all_localizations :
    ¬ (∀ (q : Ideal ℕ) [q.IsPrime], q ∈ (Ideal.span {(4 : ℕ)}).minimalPrimes →
        algebraMap ℕ (Localization.AtPrime q) 1 ∈
          (Ideal.map (algebraMap ℕ (Localization.AtPrime q)) (Ideal.span {(4 : ℕ)})).radical) := by
  intro h
  obtain ⟨n, hn⟩ :=
    (Ideal.mem_radical_iff_forall_minimalPrimes_localization (Ideal.span {(4 : ℕ)}) 1).mpr h
  norm_num [Ideal.mem_span_singleton] at hn

/-- Every element passes the minimal-prime localization tests for the unit ideal,
including in a trivial semiring. -/
private theorem top_localization_tests {R : Type*} [CommSemiring R] (x : R) :
    ∀ (q : Ideal R) [q.IsPrime], q ∈ (⊤ : Ideal R).minimalPrimes →
      algebraMap R (Localization.AtPrime q) x ∈
        (Ideal.map (algebraMap R (Localization.AtPrime q)) ⊤).radical := by
  apply (Ideal.mem_radical_iff_forall_minimalPrimes_localization ⊤ x).mp
  simp only [Ideal.radical_top, Submodule.mem_top]
