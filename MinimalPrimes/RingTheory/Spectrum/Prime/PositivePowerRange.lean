/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PositivePowerRange
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Prime-spectrum injectivity from positive powers in the image

For a homomorphism of commutative semirings, if every target element has a positive
power in the image, pullback on prime spectra is injective. This follows by
reflecting ideal containment in both directions, since prime ideals are radical.
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]

/-- Pullback on prime spectra is injective if every target element has a positive
power in the image of the homomorphism. -/
theorem comap_injective_of_pos_pow_mem_range (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) :
    Function.Injective (comap f) := by
  intro x y h
  have hxy : x.asIdeal.comap f = y.asIdeal.comap f := by
    simpa only [comap_asIdeal] using congrArg PrimeSpectrum.asIdeal h
  have hrad (p : PrimeSpectrum S) : p.asIdeal.IsRadical := by
    apply Ideal.IsPrime.isRadical
    have hp : p.asIdeal ∈ Set.range
        (PrimeSpectrum.asIdeal : PrimeSpectrum S → Ideal S) := ⟨p, rfl⟩
    rw [range_asIdeal] at hp
    exact hp
  apply le_antisymm
  · exact (asIdeal_le_asIdeal x y).mp
      ((Ideal.comap_le_comap_iff_of_pos_pow_mem_range f hf x.asIdeal y.asIdeal
        (hrad y)).mp hxy.le)
  · exact (asIdeal_le_asIdeal y x).mp
      ((Ideal.comap_le_comap_iff_of_pos_pow_mem_range f hf y.asIdeal x.asIdeal
        (hrad x)).mp hxy.ge)

end PrimeSpectrum
