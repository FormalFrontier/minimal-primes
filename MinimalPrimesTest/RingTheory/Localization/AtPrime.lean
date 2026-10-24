/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Clients of the prime-localization field criterion

The fraction localizations `ℤ → ℚ` and `ℕ → ℚ≥0` instantiate the criterion at zero.
The second uses a semifield rather than a ring. Localization of `ℤ` at `(2)` is
reduced but not a field; this is not the quotient by `(2)`.

The recovery lemma proves Mathlib's original `LocalizationPreserves` statement,
with its commutative-ring hypotheses and common universe, from the more general
reducedness theorem. It asserts the same mathematical property as
`isReduced_localizationPreserves`, without adding a public duplicate or an equality
between proofs of a proposition.
-/

@[expose] public section

universe u

private theorem localizationPreserves_isReduced :
    LocalizationPreserves.{u} (fun R _ => IsReduced R) := by
  intro R _ M S _ _ _ hR
  let : IsReduced R := hR
  exact IsReduced.of_isLocalization M S

example : (⊥ : Ideal ℤ) ∈ minimalPrimes ℤ ∧ IsReduced ℚ := by
  let : IsLocalization.AtPrime ℚ (⊥ : Ideal ℤ) := by
    change IsLocalization (⊥ : Ideal ℤ).primeCompl ℚ
    rw [Ideal.primeCompl_bot]
    exact Rat.isFractionRing
  exact (IsLocalization.AtPrime.isField_iff_mem_minimalPrimes_and_isReduced
    ℚ (⊥ : Ideal ℤ)).mp (Field.toIsField ℚ)

example : (⊥ : Ideal ℕ) ∈ minimalPrimes ℕ := by
  let : IsLocalization.AtPrime ℚ≥0 (⊥ : Ideal ℕ) := by
    change IsLocalization (⊥ : Ideal ℕ).primeCompl ℚ≥0
    rw [Ideal.primeCompl_bot]
    exact NNRat.isFractionRing
  exact (IsLocalization.AtPrime.isField_iff_mem_minimalPrimes
    ℚ≥0 (⊥ : Ideal ℕ)).mp (Semifield.toIsField ℚ≥0)

namespace Localization.AtPrime

/-- Localization of the integers at `(2)` is reduced but is not a field. -/
theorem integer_two_reduced_not_field
    [h2 : (Ideal.span {(2 : ℤ)} : Ideal ℤ).IsPrime] :
    IsReduced (Localization.AtPrime (Ideal.span {(2 : ℤ)})) ∧
      ¬ IsField (Localization.AtPrime (Ideal.span {(2 : ℤ)})) := by
  refine ⟨IsReduced.of_isLocalization (Ideal.span {(2 : ℤ)}).primeCompl _, ?_⟩
  intro hfield
  have hmin := (IsLocalization.AtPrime.isField_iff_mem_minimalPrimes
    (Localization.AtPrime (Ideal.span {(2 : ℤ)})) (Ideal.span {(2 : ℤ)})).mp hfield
  have hbot : Ideal.span {(2 : ℤ)} = ⊥ := by
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using hmin
  exact Int.prime_two.ne_zero (Ideal.span_singleton_eq_bot.mp hbot)

end Localization.AtPrime
