/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PositivePowerRange
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Prime-spectrum embeddings from positive powers in the image

For a homomorphism of commutative semirings, if every target element has a positive
power in the image, pullback on prime spectra is a topological embedding.
Injectivity follows by reflecting ideal containment in both directions, since
prime ideals are radical. For the topology, every basic open of the source
spectrum is the preimage of a basic open of the target spectrum. The proof uses
Mathlib's basic-open identities and neighborhood-basis criterion.
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

/-- Pullback on prime spectra is a topological embedding if every target element
has a positive power in the image of the homomorphism. -/
theorem isEmbedding_comap_of_pos_pow_mem_range (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) :
    Topology.IsEmbedding (comap f) := by
  have hpre (r : R) :
      comap f ⁻¹' (basicOpen r : Set (PrimeSpectrum R)) =
        (basicOpen (f r) : Set (PrimeSpectrum S)) := by
    simp only [basicOpen_eq_zeroLocus_compl, Set.preimage_compl,
      preimage_comap_zeroLocus, Set.image_singleton]
  apply Topology.IsEmbedding.mk' _ (comap_injective_of_pos_pow_mem_range f hf)
  intro p
  apply Filter.ext
  intro U
  constructor
  · intro hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    exact Filter.mem_of_superset
      ((continuous_comap f).continuousAt.preimage_mem_nhds hV) hVU
  · intro hU
    obtain ⟨V, ⟨a, rfl⟩, hp, hVU⟩ :=
      (isTopologicalBasis_basic_opens (R := S)).mem_nhds_iff.mp hU
    obtain ⟨n, hn, r, hr⟩ := hf a
    have hprea :
        comap f ⁻¹' (basicOpen r : Set (PrimeSpectrum R)) =
          (basicOpen a : Set (PrimeSpectrum S)) := by
      rw [hpre r, hr, basicOpen_pow a n hn]
    apply Filter.mem_comap.mpr
    refine ⟨(basicOpen r : Set (PrimeSpectrum R)), ?_, ?_⟩
    · apply isOpen_basicOpen.mem_nhds
      change p ∈ comap f ⁻¹' (basicOpen r : Set (PrimeSpectrum R))
      rw [hprea]
      exact hp
    · rw [hprea]
      exact hVU

end PrimeSpectrum
