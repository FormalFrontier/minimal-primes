/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Spectrum.Maximal.Map
public import Mathlib.RingTheory.Spectrum.Maximal.Topology

/-!
# Integral contraction on maximal spectra and the Zariski topology

Contraction along an integral homomorphism of commutative rings is continuous and
closed for the canonical Zariski topologies on maximal spectra. Its image is the
trace of the prime-spectrum zero locus of the kernel. More generally, the image of
the trace of an ideal's zero locus is the trace of the contracted ideal's zero locus.

These statements allow zero rings and use the existing maximal-spectrum subspace
topology. For an integral homomorphism, a prime ideal is maximal if and only if its
contraction is maximal; the reverse implication identifies the fibres needed for
the closed-trace image calculation.

## References

The proofs reuse Mathlib's ideal lying-over and maximality results in
`Mathlib.RingTheory.Ideal.GoingUp`, its prime-spectrum integral closed-map theorem in
`Mathlib.RingTheory.Spectrum.Prime.Topology`, and the induced maximal-spectrum topology
in `Mathlib.RingTheory.Spectrum.Maximal.Topology`.
-/

@[expose] public section

universe u v

namespace MaximalSpectrum

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- The image of integral contraction is the maximal-spectrum trace of the zero locus
of the kernel. -/
theorem range_comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral) :
    Set.range (comapOfIsIntegral f hf) =
      toPrimeSpectrum ⁻¹' PrimeSpectrum.zeroLocus (RingHom.ker f : Set R) := by
  ext M
  exact mem_range_comapOfIsIntegral f hf M

/-- Integral contraction takes an ideal's maximal-spectrum zero-locus trace onto the
zero-locus trace of its contraction. -/
theorem image_comapOfIsIntegral_zeroLocus (f : R →+* S) (hf : f.IsIntegral)
    (I : Ideal S) :
    comapOfIsIntegral f hf ''
        (toPrimeSpectrum ⁻¹' PrimeSpectrum.zeroLocus (I : Set S)) =
      toPrimeSpectrum ⁻¹' PrimeSpectrum.zeroLocus (Ideal.comap f I : Set R) := by
  ext M
  constructor
  · rintro ⟨N, hN, rfl⟩
    change Ideal.comap f I ≤ (comapOfIsIntegral f hf N).asIdeal
    rw [comapOfIsIntegral_asIdeal]
    exact Ideal.comap_mono (show I ≤ N.asIdeal from hN)
  · intro hM
    let : Algebra R S := f.toAlgebra
    let : Algebra.IsIntegral R S := ⟨hf⟩
    obtain ⟨Q, hIQ, hQprime, hQM⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral M.asIdeal I
        (show I.under R ≤ M.asIdeal from hM)
    let : Q.IsPrime := hQprime
    have hcomap : Ideal.comap f Q = M.asIdeal := hQM
    have hQmax : Q.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap f hf Q
        (hcomap.symm ▸ M.isMaximal)
    refine ⟨⟨Q, hQmax⟩, hIQ, MaximalSpectrum.ext ?_⟩
    exact (comapOfIsIntegral_asIdeal f hf ⟨Q, hQmax⟩).trans hcomap

/-- Integral contraction is continuous for the canonical Zariski topologies. -/
@[fun_prop]
theorem continuous_comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral) :
    Continuous (comapOfIsIntegral f hf) := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, toPrimeSpectrum_comapOfIsIntegral] using
    (PrimeSpectrum.continuous_comap f).comp toPrimeSpectrum_continuous

/-- Integral contraction is a closed map for the canonical Zariski topologies. -/
theorem isClosedMap_comapOfIsIntegral (f : R →+* S) (hf : f.IsIntegral) :
    IsClosedMap (comapOfIsIntegral f hf) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := isClosed_induced_iff.mp hC
  have himage : comapOfIsIntegral f hf '' (toPrimeSpectrum ⁻¹' D) =
      toPrimeSpectrum ⁻¹' (PrimeSpectrum.comap f '' D) := by
    ext M
    constructor
    · rintro ⟨N, hN, rfl⟩
      exact ⟨N.toPrimeSpectrum, hN, (toPrimeSpectrum_comapOfIsIntegral f hf N).symm⟩
    · rintro ⟨q, hq, hqM⟩
      have hqmax : q.asIdeal.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_comap f hf q.asIdeal (by
          rw [← PrimeSpectrum.comap_asIdeal f q, hqM]
          exact M.isMaximal)
      let N : MaximalSpectrum S := ⟨q.asIdeal, hqmax⟩
      have hNq : N.toPrimeSpectrum = q := PrimeSpectrum.ext rfl
      refine ⟨N, ?_, ?_⟩
      · simpa only [Set.mem_preimage, hNq] using hq
      · apply toPrimeSpectrum_injective
        rw [toPrimeSpectrum_comapOfIsIntegral, hNq, hqM]
  rw [himage]
  exact ((PrimeSpectrum.isClosedMap_comap_of_isIntegral f hf) D hD).preimage
    toPrimeSpectrum_continuous

end MaximalSpectrum
