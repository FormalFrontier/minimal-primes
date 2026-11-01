/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Stone topology on spectra of products of semifields

`PrimeSpectrum.piHomeomorphUltrafilter` upgrades the zero-set classification to a
homeomorphism for the Zariski topology and the existing Stone topology on ultrafilters.
Its underlying equivalence is `PrimeSpectrum.piEquivUltrafilter`.

The inverse image of a Zariski basic open is the Stone basic set of the nonzero locus.
In the other direction, membership of any subset is tested by the function which is
one on that subset and zero elsewhere. These identities prove both continuity
directions without changing either topology. Coordinate primes form a dense subspace,
even when non-coordinate primes occur.

The index and factor universes are independent. Neither finiteness nor nonemptiness
of the index, nor additive inverses in the factors, are required.

## References

The algebraic classification is the prior Formal Frontier formalization in
`MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter`. The topology and its membership
basis are Mathlib's ultrafilter construction in `Mathlib.Topology.Compactification.StoneCech`
by Reid Barton (whose general compactification also credits Marius Stekelenburg).
The Zariski topology and its basic-open basis are Mathlib's prime-spectrum
formalization by Johan Commelin. We use Mathlib's homeomorphism and dense-embedding APIs.
-/

@[expose] public section

open Set Filter

universe u v

namespace PrimeSpectrum

variable {ι : Type u} (K : ι → Type v) [∀ i, Semifield (K i)]

private theorem piEquivUltrafilter_symm_preimage_basicOpen (f : Π i, K i) :
    (piEquivUltrafilter K).symm ⁻¹' (basicOpen f : Set (PrimeSpectrum (Π i, K i))) =
      {U : Ultrafilter ι | {i | f i ≠ 0} ∈ U} := by
  ext U
  change f ∉ U.piIdeal K ↔ {i | f i ≠ 0} ∈ U
  rw [Ultrafilter.mem_piIdeal]
  exact (Ultrafilter.compl_mem_iff_notMem (f := U) (s := {i | f i = 0})).symm

open Classical in
private theorem piEquivUltrafilter_preimage_mem (s : Set ι) :
    piEquivUltrafilter K ⁻¹' {U : Ultrafilter ι | s ∈ U} =
      (basicOpen (fun i ↦ if i ∈ s then (1 : K i) else 0) :
        Set (PrimeSpectrum (Π i, K i))) := by
  ext p
  change s ∈ p.piUltrafilter K ↔ (fun i ↦ if i ∈ s then (1 : K i) else 0) ∉ p.asIdeal
  have hz : {i | (if i ∈ s then (1 : K i) else 0) = 0} = sᶜ := by
    ext i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [← zeroSet_mem_piUltrafilter K p, hz]
  exact Ultrafilter.compl_notMem_iff.symm

/-- The prime spectrum of an arbitrary dependent product of semifields is homeomorphic
to the ultrafilter space with its existing Stone topology. The equivalence is the
zero-set classification `piEquivUltrafilter`. -/
noncomputable def piHomeomorphUltrafilter : PrimeSpectrum (Π i, K i) ≃ₜ Ultrafilter ι where
  toEquiv := piEquivUltrafilter K
  continuous_toFun := by
    apply ultrafilterBasis_is_basis.continuous_iff.mpr
    rintro _ ⟨s, rfl⟩
    change IsOpen (piEquivUltrafilter K ⁻¹' {U : Ultrafilter ι | s ∈ U})
    rw [piEquivUltrafilter_preimage_mem]
    exact isOpen_basicOpen
  continuous_invFun := by
    apply isTopologicalBasis_basic_opens.continuous_iff.mpr
    rintro _ ⟨f, rfl⟩
    change IsOpen ((piEquivUltrafilter K).symm ⁻¹'
      (basicOpen f : Set (PrimeSpectrum (Π i, K i))))
    rw [piEquivUltrafilter_symm_preimage_basicOpen]
    exact ultrafilter_isOpen_basic _

/-- The Stone homeomorphism retains the existing algebraic equivalence exactly. -/
@[simp]
theorem piHomeomorphUltrafilter_toEquiv :
    (piHomeomorphUltrafilter K).toEquiv = piEquivUltrafilter K := rfl

/-- The forward map is the prime's zero-set ultrafilter. -/
@[simp]
theorem piHomeomorphUltrafilter_apply (p : PrimeSpectrum (Π i, K i)) :
    piHomeomorphUltrafilter K p = p.piUltrafilter K := rfl

/-- The inverse map has precisely the existing ultrafilter ideal. -/
@[simp]
theorem piHomeomorphUltrafilter_symm_asIdeal (U : Ultrafilter ι) :
    ((piHomeomorphUltrafilter K).symm U).asIdeal = U.piIdeal K := rfl

/-- Primes agree if membership of every subset in their Stone coordinates agrees. -/
theorem piHomeomorphUltrafilter_ext {p q : PrimeSpectrum (Π i, K i)}
    (h : ∀ s : Set ι, s ∈ piHomeomorphUltrafilter K p ↔ s ∈ piHomeomorphUltrafilter K q) :
    p = q :=
  (piHomeomorphUltrafilter K).injective (Ultrafilter.ext h)

/-- Pulling back a Zariski basic open along the inverse classification tests the
nonzero locus, not the zero locus. -/
theorem piHomeomorphUltrafilter_symm_preimage_basicOpen (f : Π i, K i) :
    (piHomeomorphUltrafilter K).symm ⁻¹'
        (basicOpen f : Set (PrimeSpectrum (Π i, K i))) =
      {U : Ultrafilter ι | {i | f i ≠ 0} ∈ U} :=
  piEquivUltrafilter_symm_preimage_basicOpen K f

open Classical in
/-- A Stone basic set pulls back to the basic open of the one-on-set, zero-off-set
function. This tests membership of arbitrary, including infinite, subsets. -/
theorem piHomeomorphUltrafilter_preimage_mem (s : Set ι) :
    piHomeomorphUltrafilter K ⁻¹' {U : Ultrafilter ι | s ∈ U} =
      (basicOpen (fun i ↦ if i ∈ s then (1 : K i) else 0) :
        Set (PrimeSpectrum (Π i, K i))) :=
  piEquivUltrafilter_preimage_mem K s

/-- The image of a Zariski basic open is the Stone basic set of its nonzero locus. -/
theorem piHomeomorphUltrafilter_image_basicOpen (f : Π i, K i) :
    piHomeomorphUltrafilter K '' (basicOpen f : Set (PrimeSpectrum (Π i, K i))) =
      {U : Ultrafilter ι | {i | f i ≠ 0} ∈ U} := by
  rw [(piHomeomorphUltrafilter K).image_eq_preimage_symm,
    piHomeomorphUltrafilter_symm_preimage_basicOpen]

/-- Pure ultrafilters correspond to labelled coordinate kernels. -/
theorem piHomeomorphUltrafilter_symm_pure_asIdeal (i : ι) :
    ((piHomeomorphUltrafilter K).symm (pure i)).asIdeal =
      RingHom.ker (Pi.evalRingHom K i) := by
  simp

/-- Coordinate primes are dense in the spectrum, even for infinite products.
This transports Mathlib's density of pure ultrafilters through the homeomorphism. -/
theorem denseRange_piHomeomorphUltrafilter_symm_pure :
    DenseRange (fun i : ι ↦ (piHomeomorphUltrafilter K).symm (pure i)) := by
  change Dense (Set.range ((piHomeomorphUltrafilter K).symm ∘ (pure : ι → Ultrafilter ι)))
  rw [Set.range_comp]
  exact (piHomeomorphUltrafilter K).symm.isDenseEmbedding.dense_image.mpr denseRange_pure

end PrimeSpectrum
