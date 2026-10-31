/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Spectrum.Prime.PositivePowerRange

/-!
# Surjective compatibility for prime-spectrum pullback

The positive-power criterion recovers injectivity of pullback along a surjective
homomorphism by taking exponent one.
-/

@[expose] public section

universe u v

example {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (PrimeSpectrum.comap f) := by
  apply PrimeSpectrum.comap_injective_of_pos_pow_mem_range f
  intro x
  obtain ⟨a, ha⟩ := hf x
  refine ⟨1, Nat.zero_lt_one, a, ?_⟩
  simpa only [pow_one] using ha
