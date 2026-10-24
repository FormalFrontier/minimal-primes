/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Minimal primes detected by localized radicals

For an arbitrary ideal `I` of a commutative semiring, localization at a prime ideal `q`
identifies the radical of the extended ideal with the extension of `q` exactly when `q`
is minimal over `I`. No containment hypothesis is required: the equality itself forces
`I ≤ q` through the prime-ideal correspondence for localization.

## References

This module uses Mathlib's `IsLocalization.minimalPrimes_map`,
`Ideal.radical_minimalPrimes`, and the prime-ideal correspondence for localization at a
prime. The reverse implication of the equivalence is Mathlib's
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`, formalized by Andrew Yang.
-/

@[expose] public section

universe u v

namespace IsLocalization.AtPrime

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- If the radical of an extended ideal in the localization at `q` equals the extension
of `q`, then `q` is minimal over the original ideal. In particular, the equality forces
containment in `q`. This uses Mathlib's minimal-prime and prime-ideal correspondences. -/
theorem mem_minimalPrimes_of_radical_map_eq
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime A q] (I : Ideal R)
    (h : (I.map (algebraMap R A)).radical = q.map (algebraMap R A)) :
    q ∈ I.minimalPrimes := by
  have : (q.map (algebraMap R A)).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime (S := A) q le_rfl
  have hmin : q.map (algebraMap R A) ∈ (I.map (algebraMap R A)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, h, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  simpa only [IsLocalization.minimalPrimes_map q.primeCompl A I, Set.mem_preimage,
    Ideal.under_map_of_isLocalizationAtPrime (S := A) q le_rfl] using hmin

/-- The radical of an extended ideal in the localization at `q` equals the extension
of `q` if and only if `q` is minimal over that ideal. The forward implication needs no
separate containment hypothesis; the reverse implication is Mathlib's
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`. -/
theorem radical_map_eq_iff_mem_minimalPrimes
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime A q] (I : Ideal R) :
    (I.map (algebraMap R A)).radical = q.map (algebraMap R A) ↔ q ∈ I.minimalPrimes :=
  ⟨mem_minimalPrimes_of_radical_map_eq q I, radical_map_of_mem_minimalPrimes A q I⟩

end IsLocalization.AtPrime
