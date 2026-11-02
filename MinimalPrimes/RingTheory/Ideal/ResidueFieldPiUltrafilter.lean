/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.RingTheory.Ideal.PrimePiUltrafilter
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue fields of dependent ultrafilter products

For independently universed field fibres, the residue field of the ultrafilter's
zero-set ideal is canonically isomorphic to the existing `Filter.Product`.
The equivalence commutes with the map from all dependent sections, and is uniquely
determined by that property. Fibrewise field homomorphisms give a commuting square
with the existing residue-field and reduced-product maps.

The construction composes the quotient-to-residue-field equivalence at a maximal
ideal with the first isomorphism theorem. It requires no field structure on the
reduced-product carrier, no common characteristic and no extra index hypothesis.
The dependent Product carrier and its algebra reuse the work of Abhimanyu Pallavi
Sudhir and Yury Kudryashov, together with Mathlib's quotient and residue-field APIs.

## References

* Mathlib `Order.Filter.Germ.Basic` and `Order.Filter.FilterProduct`: the dependent
  `Filter.Product` carrier and the ultraproduct inversion argument, by Abhimanyu
  Pallavi Sudhir and Yury Kudryashov.
* Mathlib `RingTheory.Congruence.Hom`: the quotient and descended-map interfaces
  used by the dependent Product algebra, by Antoine Chambert-Loir.
* Mathlib `RingTheory.Ideal.Quotient.Operations`: the quotient first-isomorphism
  theorem, by Kenny Lau and Patrick Massot.
* Mathlib `RingTheory.LocalRing.ResidueField.Ideal`: Andrew Yang's ideal residue
  fields, the quotient-to-residue-field bijection at maximal ideals and induced maps.
  These use the local-ring residue fields of `RingTheory.LocalRing.ResidueField.Defs`
  and the prime localizations of `RingTheory.Localization.AtPrime.Basic`.
-/

@[expose] public section

open Filter

universe u v w

namespace Ultrafilter

variable {ι : Type u} (K : ι → Type v) [∀ i, Field (K i)] (U : Ultrafilter ι)

/-- The canonical residue comparison, over the ring of all dependent sections. -/
noncomputable def residueFieldProductEquiv :
    (U.piIdeal K).ResidueField ≃+* (U : Filter ι).Product K :=
  (RingEquiv.ofBijective
    (algebraMap ((∀ i, K i) ⧸ U.piIdeal K) (U.piIdeal K).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (U.piIdeal K))).symm.trans
    ((Ideal.quotEquivOfEq (piIdeal_eq_ker_productMk K U)).trans
      (RingHom.quotientKerEquivOfSurjective
        (Filter.productRingCon (U : Filter ι) K).mk'_surjective))

/-- The comparison sends the residue of every section to its reduced-product class. -/
@[simp]
theorem residueFieldProductEquiv_algebraMap (r : ∀ i, K i) :
    residueFieldProductEquiv K U (algebraMap _ (U.piIdeal K).ResidueField r) =
      (Filter.productRingCon (U : Filter ι) K).mk' r := by
  let j := RingEquiv.ofBijective
    (algebraMap ((∀ i, K i) ⧸ U.piIdeal K) (U.piIdeal K).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (U.piIdeal K))
  have hj : j.symm (algebraMap _ (U.piIdeal K).ResidueField r) =
      Ideal.Quotient.mk (U.piIdeal K) r := by
    apply j.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  change ((Ideal.quotEquivOfEq (piIdeal_eq_ker_productMk K U)).trans
    (RingHom.quotientKerEquivOfSurjective
      (Filter.productRingCon (U : Filter ι) K).mk'_surjective))
        (j.symm (algebraMap _ (U.piIdeal K).ResidueField r)) = _
  rw [hj]
  rfl

/-- The characteristic equation as equality of homomorphisms over the section ring. -/
theorem residueFieldProductEquiv_comp_algebraMap :
    (residueFieldProductEquiv K U).toRingHom.comp
      (algebraMap _ (U.piIdeal K).ResidueField) =
      (Filter.productRingCon (U : Filter ι) K).mk' := by
  apply RingHom.ext
  exact residueFieldProductEquiv_algebraMap K U

/-- The inverse characteristic equation also holds on every dependent section. -/
@[simp]
theorem residueFieldProductEquiv_symm_coe (r : ∀ i, K i) :
    (residueFieldProductEquiv K U).symm
      (r : (U : Filter ι).Product K) = algebraMap _ (U.piIdeal K).ResidueField r := by
  apply (residueFieldProductEquiv K U).injective
  exact ((residueFieldProductEquiv K U).apply_symm_apply
    (r : (U : Filter ι).Product K)).trans
      (residueFieldProductEquiv_algebraMap K U r).symm

/-- Agreement on all section residues uniquely determines the comparison. -/
theorem residueFieldProductEquiv_unique
    (e : (U.piIdeal K).ResidueField ≃+* (U : Filter ι).Product K)
    (h : ∀ r : ∀ i, K i,
      e (algebraMap _ (U.piIdeal K).ResidueField r) =
        (Filter.productRingCon (U : Filter ι) K).mk' r) :
    e = residueFieldProductEquiv K U := by
  apply RingEquiv.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective (U.piIdeal K) x
  exact (h r).trans (residueFieldProductEquiv_algebraMap K U r).symm

section Naturality

variable {L : ι → Type w} [∀ i, Field (L i)]

/-- Fibrewise field maps pull back the zero-set ideal. The exact legacy telescope
is retained; `piIdeal_map_comap_piRingHom` provides the weaker, general-index core. -/
theorem piIdeal_comap_piRingHom (φ : ∀ i, K i →+* L i) :
    U.piIdeal K = (U.piIdeal L).comap
      (RingHom.pi fun i => (φ i).comp (Pi.evalRingHom K i)) := by
  simpa only [Ultrafilter.map_id, id_eq] using piIdeal_map_comap_piRingHom K id U φ

/-- The same canonical comparison commutes with the stock fibrewise maps. -/
@[simp]
theorem residueFieldProductEquiv_map (φ : ∀ i, K i →+* L i)
    (x : (U.piIdeal K).ResidueField) :
    residueFieldProductEquiv L U
      (Ideal.ResidueField.map (U.piIdeal K) (U.piIdeal L)
        (RingHom.pi fun i => (φ i).comp (Pi.evalRingHom K i))
        -- Keep this consumer explicit to exercise the legacy universe/class interface.
        (@piIdeal_comap_piRingHom.{u, v, w} ι K
          (inferInstance : ∀ i, Field (K i)) U L
          (inferInstance : ∀ i, Field (L i)) φ) x) =
      Filter.Product.mapRingHom (U : Filter ι) φ (residueFieldProductEquiv K U x) := by
  obtain ⟨r, rfl⟩ := Ideal.algebraMap_residueField_surjective (U.piIdeal K) x
  rw [Ideal.ResidueField.map_algebraMap, residueFieldProductEquiv_algebraMap,
    residueFieldProductEquiv_algebraMap]
  rfl

/-- The naturality square, expressed as an equality of ring homomorphisms. -/
theorem residueFieldProductEquiv_naturality (φ : ∀ i, K i →+* L i) :
    (residueFieldProductEquiv L U).toRingHom.comp
      (Ideal.ResidueField.map (U.piIdeal K) (U.piIdeal L)
        (RingHom.pi fun i => (φ i).comp (Pi.evalRingHom K i))
        (piIdeal_comap_piRingHom K U φ)) =
      (Filter.Product.mapRingHom (U : Filter ι) φ).comp
        (residueFieldProductEquiv K U).toRingHom := by
  apply RingHom.ext
  exact residueFieldProductEquiv_map K U φ

end Naturality

end Ultrafilter
