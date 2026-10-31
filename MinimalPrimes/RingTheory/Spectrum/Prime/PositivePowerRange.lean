/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PositivePowerRange
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Prime-spectrum embeddings from positive powers in the image

For a homomorphism of commutative semirings, if every target element has a positive
power in the image, pullback on prime spectra is a topological embedding.
Injectivity follows by reflecting ideal containment in both directions, since
prime ideals are radical. For the topology, every basic open of the source
spectrum is the preimage of a basic open of the target spectrum. The proof uses
Mathlib's basic-open identities and neighborhood-basis criterion.

For commutative rings, pullback is a closed embedding. The proof applies
Mathlib's spectrum homeomorphism criterion to the induced injection from the
quotient by the kernel, then composes with the closed embedding for the quotient map.

## References

- Mathlib's `PrimeSpectrum.isHomeomorph_comap`, the homeomorphism criterion
  associated with Stacks Project, Tag 0BR8.
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

section CommSemiring

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

end CommSemiring

section CommRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Pullback on prime spectra is a closed embedding if every target element has a
positive power in the image of the ring homomorphism.

Apply Mathlib's `PrimeSpectrum.isHomeomorph_comap` after quotienting by the kernel,
then compose with the closed embedding associated to the quotient map. -/
theorem isClosedEmbedding_comap_of_pos_pow_mem_range (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) :
    Topology.IsClosedEmbedding (comap f) := by
  have hzero : ∀ a : R, a ∈ RingHom.ker f → f a = 0 :=
    fun _ ha => RingHom.mem_ker.mp ha
  let g := Ideal.Quotient.lift (RingHom.ker f) f hzero
  have hgpow : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ g.range := by
    intro x
    obtain ⟨n, hn, a, ha⟩ := hf x
    refine ⟨n, hn, RingHom.mem_range.mpr ⟨Ideal.Quotient.mk _ a, ?_⟩⟩
    simpa only [g, Ideal.Quotient.lift_mk] using ha
  have hginj : Function.Injective g :=
    RingHom.lift_injective_of_ker_le_ideal (RingHom.ker f) hzero le_rfl
  have hg := isHomeomorph_comap g hgpow (by
    rw [(RingHom.injective_iff_ker_eq_bot g).mp hginj]
    exact bot_le)
  have hq := isClosedEmbedding_comap_of_surjective
    (S := R ⧸ RingHom.ker f) (f := Ideal.Quotient.mk (RingHom.ker f))
    (Ideal.Quotient.mk_surjective (I := RingHom.ker f))
  rw [← Ideal.Quotient.lift_comp_mk (RingHom.ker f) f hzero, comap_comp]
  exact hq.comp hg.isClosedEmbedding

end CommRing

end PrimeSpectrum
