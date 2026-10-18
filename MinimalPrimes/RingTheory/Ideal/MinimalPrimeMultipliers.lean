/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Multipliers outside a minimal prime

Let `q` be a minimal prime over an ideal `I` of a commutative semiring. Every element
`x ∈ q` has a multiplier `s ∉ q` such that `s * x ∈ I.radical`. For `I = ⊥`, the
product is nilpotent. The multiplier avoids the chosen minimal prime, not merely `I`.
No Noetherian, finiteness or reducedness hypothesis is needed.

The proof localizes at `q`, where the radical of the image of `I` is the image of
`q`, and clears a denominator from the image of `I.radical`.

## References

The proof uses Mathlib's
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`, `IsLocalization.map_radical`
and `IsLocalization.algebraMap_mem_map_algebraMap_iff`. The zero-ideal specialization
uses Mathlib's `mem_nilradical`.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R] {I q : Ideal R} {x : R}

/-- An element of a minimal prime over `I` has a multiplier outside that same prime
whose product lies in `I.radical`. This holds in every commutative semiring. -/
theorem exists_mul_mem_radical_of_mem_minimalPrimes (hq : q ∈ I.minimalPrimes)
    (hx : x ∈ q) : ∃ s ∉ q, s * x ∈ I.radical := by
  letI : q.IsPrime := hq.isPrime
  have hxmap : algebraMap R (Localization.AtPrime q) x ∈
      I.radical.map (algebraMap R (Localization.AtPrime q)) := by
    rw [IsLocalization.map_radical q.primeCompl (Localization.AtPrime q),
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q I hq]
    exact mem_map_of_mem _ hx
  simpa only [mem_primeCompl_iff] using
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      q.primeCompl (Localization.AtPrime q) I.radical x).mp hxmap

/-- An element of a minimal prime of a commutative semiring has a multiplier outside
that same prime whose product is nilpotent. No reducedness hypothesis is imposed. -/
theorem exists_isNilpotent_mul_of_mem_minimalPrimes (hq : q ∈ minimalPrimes R)
    (hx : x ∈ q) : ∃ s ∉ q, IsNilpotent (s * x) := by
  obtain ⟨s, hs, hsx⟩ := exists_mul_mem_radical_of_mem_minimalPrimes (I := ⊥) hq hx
  exact ⟨s, hs, mem_nilradical.mp hsx⟩

end Ideal
