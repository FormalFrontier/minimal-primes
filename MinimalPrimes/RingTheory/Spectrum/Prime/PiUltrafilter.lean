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
# Ultrafilter coordinates and fibers of product spectra

For arbitrary commutative semiring factors, `PrimeSpectrum.piUltrafilterMap` is
continuous for the Zariski and Stone topologies. For commutative ring factors,
`PrimeSpectrum.piUltrafilterFiberHomeomorph` identifies each fiber with the spectrum
of the existing zero-set quotient. Its forward map is quotient comap, including
when the quotient is the zero ring and its spectrum and fiber are empty.

For semifield factors, `PrimeSpectrum.piHomeomorphUltrafilter` upgrades the zero-set
classification to a homeomorphism for the Zariski topology and the existing Stone
topology on ultrafilters.
Its underlying equivalence is `PrimeSpectrum.piEquivUltrafilter`.

The inverse image of a Zariski basic open is the Stone basic set of the nonzero locus.
In the other direction, membership of any subset is tested by the function which is
one on that subset and zero elsewhere. These identities prove both continuity
directions without changing either topology. Coordinate primes form a dense subspace,
even when non-coordinate primes occur.

The index and factor universes are independent. Neither finiteness nor nonemptiness
of the index is required. The coordinate and semifield classification need no
additive inverses; the quotient-fiber theorem assumes commutative ring factors.

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

universe u v w x

namespace PrimeSpectrum

variable {ι : Type u}

section CommSemiring

variable (R : ι → Type v) [∀ i, CommSemiring (R i)]

open Classical in
/-- A Stone membership basic set pulls back to the Zariski basic open of its
one-on-set, zero-off-set function. -/
theorem piUltrafilterMap_preimage_mem (s : Set ι) :
    piUltrafilterMap R ⁻¹' {U : Ultrafilter ι | s ∈ U} =
      (basicOpen (fun i ↦ if i ∈ s then (1 : R i) else 0) :
        Set (PrimeSpectrum (Π i, R i))) := by
  ext p
  exact mem_piUltrafilterMap R p s

/-- The canonical ultrafilter coordinate is continuous, without nontriviality,
nonemptiness or finiteness hypotheses on the factors or index. -/
theorem continuous_piUltrafilterMap : Continuous (piUltrafilterMap R) := by
  apply ultrafilterBasis_is_basis.continuous_iff.mpr
  rintro _ ⟨s, rfl⟩
  change IsOpen (piUltrafilterMap R ⁻¹' {U : Ultrafilter ι | s ∈ U})
  rw [piUltrafilterMap_preimage_mem]
  exact isOpen_basicOpen

/-- Coordinate comap has the corresponding principal ultrafilter coordinate,
even when the selected factor is a zero semiring. -/
@[simp]
theorem piUltrafilterMap_comap_evalRingHom (i : ι) (p : PrimeSpectrum (R i)) :
    piUltrafilterMap R (comap (Pi.evalRingHom R i) p) = pure i := by
  apply (piIdeal_le_asIdeal_iff_piUltrafilterMap_eq R (pure i) _).1
  rw [Ultrafilter.piIdeal_pure]
  intro f hf
  change f i = 0 at hf
  change f i ∈ p.asIdeal
  rw [hf]
  exact p.asIdeal.zero_mem

end CommSemiring

section CommRing

variable (R : ι → Type v) [∀ i, CommRing (R i)]

/-- The range of quotient comap is exactly the prescribed ultrafilter fiber. -/
theorem range_comap_piIdeal_quotient (U : Ultrafilter ι) :
    Set.range (comap (Ideal.Quotient.mk (U.piIdeal R))) =
      {p : PrimeSpectrum (Π i, R i) | piUltrafilterMap R p = U} := by
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  ext p
  change U.piIdeal R ≤ p.asIdeal ↔ piUltrafilterMap R p = U
  exact piIdeal_le_asIdeal_iff_piUltrafilterMap_eq R U p

/-- Quotient comap canonically identifies the spectrum of the existing zero-set
quotient with its ultrafilter fiber, with the inherited subtype topology. Neither
the ideal nor the quotient is assumed proper, prime or nontrivial. -/
noncomputable def piUltrafilterFiberHomeomorph (U : Ultrafilter ι) :
    PrimeSpectrum ((Π i, R i) ⧸ U.piIdeal R) ≃ₜ
      {p : PrimeSpectrum (Π i, R i) // piUltrafilterMap R p = U} :=
  (isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk (U.piIdeal R))
    Ideal.Quotient.mk_surjective).toHomeomorph.trans
      (Homeomorph.setCongr (range_comap_piIdeal_quotient R U))

/-- The forward value is exactly the canonical quotient comap. -/
@[simp]
theorem piUltrafilterFiberHomeomorph_apply_val (U : Ultrafilter ι)
    (x : PrimeSpectrum ((Π i, R i) ⧸ U.piIdeal R)) :
    (piUltrafilterFiberHomeomorph R U x).val =
      comap (Ideal.Quotient.mk (U.piIdeal R)) x := rfl

/-- The inverse prime has the image of the fiber prime as its underlying ideal. -/
@[simp]
theorem piUltrafilterFiberHomeomorph_symm_asIdeal (U : Ultrafilter ι)
    (p : {p : PrimeSpectrum (Π i, R i) // piUltrafilterMap R p = U}) :
    ((piUltrafilterFiberHomeomorph R U).symm p).asIdeal =
      Ideal.map (Ideal.Quotient.mk (U.piIdeal R)) p.val.asIdeal := by
  have h : comap (Ideal.Quotient.mk (U.piIdeal R))
      ((piUltrafilterFiberHomeomorph R U).symm p) = p.val := by
    calc
      _ = (piUltrafilterFiberHomeomorph R U
          ((piUltrafilterFiberHomeomorph R U).symm p)).val :=
        (piUltrafilterFiberHomeomorph_apply_val R U _).symm
      _ = p.val :=
        congrArg Subtype.val ((piUltrafilterFiberHomeomorph R U).apply_symm_apply p)
  have hI := congrArg (fun x : PrimeSpectrum (Π i, R i) => x.asIdeal) h
  calc
    _ = Ideal.map (Ideal.Quotient.mk (U.piIdeal R))
        (Ideal.comap (Ideal.Quotient.mk (U.piIdeal R))
          ((piUltrafilterFiberHomeomorph R U).symm p).asIdeal) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
    _ = _ := congrArg (Ideal.map (Ideal.Quotient.mk (U.piIdeal R))) hI

/-- Evaluation comap identifies a factor spectrum with the principal fiber.
Together with the surjective-comap embedding, this gives the canonical
homeomorphism onto that fiber, including when the factor is a zero ring. -/
theorem range_comap_evalRingHom (i : ι) :
    Set.range (comap (Pi.evalRingHom R i)) =
      {p : PrimeSpectrum (Π i, R i) | piUltrafilterMap R p = pure i} := by
  rw [_root_.range_comap_of_surjective _ _ (Function.surjective_eval _)]
  ext p
  change RingHom.ker (Pi.evalRingHom R i) ≤ p.asIdeal ↔
    piUltrafilterMap R p = pure i
  rw [← Ultrafilter.piIdeal_pure R i]
  exact piIdeal_le_asIdeal_iff_piUltrafilterMap_eq R (pure i) p

end CommRing

variable (K : ι → Type v) [∀ i, Semifield (K i)]

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
  exact mem_piUltrafilterMap K p s

/-- The prime spectrum of an arbitrary dependent product of semifields is homeomorphic
to the ultrafilter space with its existing Stone topology. The equivalence is the
zero-set classification `piEquivUltrafilter`. -/
noncomputable def piHomeomorphUltrafilter : PrimeSpectrum (Π i, K i) ≃ₜ Ultrafilter ι where
  toEquiv := piEquivUltrafilter K
  continuous_toFun := continuous_piUltrafilterMap K
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

/-- The general coordinate agrees with the legacy Stone homeomorphism. -/
theorem piUltrafilterMap_eq_piHomeomorphUltrafilter (p : PrimeSpectrum (Π i, K i)) :
    piUltrafilterMap K p = piHomeomorphUltrafilter K p := rfl

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

section Naturality

variable {κ : Type w} (L : κ → Type x) [∀ j, Semifield (L j)]

/-- The spectrum-to-ultrafilter homeomorphism is natural for dependent index maps
and fibrewise semifield homomorphisms. No injectivity of either the index map or
the product homomorphism is required. -/
theorem piHomeomorphUltrafilter_comap_piRingHom (g : κ → ι)
    (φ : ∀ j, K (g j) →+* L j) (p : PrimeSpectrum (Π j, L j)) :
    piHomeomorphUltrafilter K
        (comap (RingHom.pi fun j => (φ j).comp (Pi.evalRingHom K (g j))) p) =
      Ultrafilter.map g (piHomeomorphUltrafilter L p) := by
  apply piIdeal_injective K
  simpa only [piHomeomorphUltrafilter_apply, piIdeal_piUltrafilter, comap_asIdeal] using
    (Ultrafilter.piIdeal_map_comap_piRingHom K g (p.piUltrafilter L) φ).symm

/-- The inverse classification carries ultrafilter pushforward to spectral pullback. -/
@[simp]
theorem comap_piHomeomorphUltrafilter_symm (g : κ → ι)
    (φ : ∀ j, K (g j) →+* L j) (U : Ultrafilter κ) :
    comap (RingHom.pi fun j => (φ j).comp (Pi.evalRingHom K (g j)))
        ((piHomeomorphUltrafilter L).symm U) =
      (piHomeomorphUltrafilter K).symm (Ultrafilter.map g U) := by
  apply (piHomeomorphUltrafilter K).injective
  rw [piHomeomorphUltrafilter_comap_piRingHom K L]
  simp

end Naturality

/-- Precomposition of dependent sections corresponds to pushforward of ultrafilters. -/
theorem piHomeomorphUltrafilter_comap_precomp {κ : Type w} (g : κ → ι)
    (p : PrimeSpectrum (Π j, K (g j))) :
    piHomeomorphUltrafilter K (comap (RingHom.pi fun j => Pi.evalRingHom K (g j)) p) =
      Ultrafilter.map g (piHomeomorphUltrafilter (fun j => K (g j)) p) := by
  simpa only [RingHom.id_comp] using
    piHomeomorphUltrafilter_comap_piRingHom K (fun j => K (g j)) g
      (fun j => RingHom.id (K (g j))) p

/-- Fibrewise semifield homomorphisms preserve the ultrafilter coordinate. -/
theorem piHomeomorphUltrafilter_comap_piRingHom_sameIndex
    {L : ι → Type w} [∀ i, Semifield (L i)] (φ : ∀ i, K i →+* L i)
    (p : PrimeSpectrum (Π i, L i)) :
    piHomeomorphUltrafilter K
        (comap (RingHom.pi fun i => (φ i).comp (Pi.evalRingHom K i)) p) =
      piHomeomorphUltrafilter L p := by
  simpa only [Ultrafilter.map_id, id_eq] using
    piHomeomorphUltrafilter_comap_piRingHom K L id φ p

end PrimeSpectrum
