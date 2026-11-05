/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyFinite

/-!
# Topological Krull dimension, closed covers and irreducible components

The topological Krull dimension of a space is the supremum of the dimensions of a jointly
surjective family of closed embeddings whose images form a locally finite family. The
ambient space, index type and domain spaces have independent universes, and all spaces
retain their given topologies. The closed-subspace form uses the induced topologies.

The dimension also equals the supremum of the dimensions of the canonical irreducible
components, each with its induced subspace topology. The component family need not be
locally finite: Mathlib's whole-set extension theorem places every irreducible closed
set in some maximal irreducible component, and each component is closed.

The supporting containment theorem applies to any irreducible set, without assuming
that it is closed. For finite families, local finiteness follows from
`locallyFinite_of_finite`; containment then agrees with the forward implication of
Mathlib's `isIrreducible_iff_sUnion_isClosed`, indexing a finite collection by its
membership subtype.

For a closed embedding, the existing `TopologicalSpace.IrreducibleCloseds.map` has range
exactly the irreducible closed subsets contained in the embedding's range, and preserves
height in the canonical inclusion orders. No new order or topology is introduced.

The supremum is in `WithBot ℕ∞`: an empty-index cover of the empty space has dimension
`⊥`, not zero. Infinite covers and unbounded dimensions are included, without requiring
that a member attain the supremum.

## References

* Mathlib's `Mathlib.Topology.Irreducible` for canonical irreducible components, their
  closedness and extension of whole irreducible sets to maximal components, and
  `Mathlib.Topology.LocallyFinite` for locally finite families.
* Mathlib's `Mathlib.Topology.Sets.Closeds` for the canonical irreducible-closed inclusion
  order and its continuous map.
* Mathlib's `Mathlib.Topology.KrullDimension` and `Mathlib.Order.KrullDimension` for
  topological dimension, embedding monotonicity and the empty-safe supremum of heights.
* The open-cover dimension theorem in `MinimalPrimes.Topology.KrullDimension.OpenCover`.
-/

@[expose] public section

universe u v w

/-- An irreducible set covered by a locally finite family of closed sets is contained
in one member. The irreducible set need not be closed. -/
theorem IsIrreducible.exists_subset_of_locallyFinite_isClosed_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    {A : Set X} (hA : IsIrreducible A)
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hfin : LocallyFinite C) (hcov : A ⊆ ⋃ i, C i) :
    ∃ i, A ⊆ C i := by
  classical
  obtain ⟨x, hxA⟩ := hA.nonempty
  obtain ⟨U, ⟨hxU, hU⟩, hUfin⟩ := hfin.exists_mem_basis (nhds_basis_opens x)
  let t : Finset (Set X) := hUfin.toFinset.image C
  have ht_closed : ∀ Z ∈ t, IsClosed Z := by
    intro Z hZ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ
    exact hC i
  have hAU : A ∩ U ⊆ ⋃₀ (t : Set (Set X)) := by
    intro y hy
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp (hcov hy.1)
    refine Set.mem_sUnion.mpr ⟨C i, ?_, hyi⟩
    exact Finset.mem_image.mpr ⟨i, hUfin.mem_toFinset.mpr ⟨y, hyi, hy.2⟩, rfl⟩
  have ht : IsClosed (⋃₀ (t : Set (Set X))) :=
    t.finite_toSet.isClosed_sUnion ht_closed
  -- The nonempty relative-open piece is dense in `A`.
  have hAt : A ⊆ ⋃₀ (t : Set (Set X)) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hA.isPreirreducible hU
      ⟨x, hxA, hxU⟩).trans (closure_minimal hAU ht)
  obtain ⟨Z, hZ, hAZ⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hA t ht_closed hAt
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ
  exact ⟨i, hAZ⟩

private theorem TopologicalSpace.IrreducibleCloseds.coe_map_of_isClosedEmbedding
    {D : Type w} {E : Type u} [TopologicalSpace D] [TopologicalSpace E]
    {g : D → E} (hg : Topology.IsClosedEmbedding g)
    (Z : TopologicalSpace.IrreducibleCloseds D) :
    (TopologicalSpace.IrreducibleCloseds.map g hg.continuous Z : Set E) =
      g '' (Z : Set D) := by
  rw [TopologicalSpace.IrreducibleCloseds.coe_map, hg.closure_image_eq,
    Z.isClosed.closure_eq]

/-- For a closed embedding, the existing map on irreducible closed sets has range
exactly the ambient irreducible closed sets contained in the embedding's range. -/
theorem TopologicalSpace.IrreducibleCloseds.range_map_of_isClosedEmbedding
    {D : Type w} {E : Type u} [TopologicalSpace D] [TopologicalSpace E]
    {g : D → E} (hg : Topology.IsClosedEmbedding g) :
    Set.range (TopologicalSpace.IrreducibleCloseds.map g hg.continuous) =
      {Z : TopologicalSpace.IrreducibleCloseds E | (Z : Set E) ⊆ Set.range g} := by
  ext Z
  constructor
  · rintro ⟨W, rfl⟩
    change (TopologicalSpace.IrreducibleCloseds.map g hg.continuous W : Set E) ⊆ Set.range g
    rw [TopologicalSpace.IrreducibleCloseds.coe_map_of_isClosedEmbedding hg]
    exact Set.image_subset_range _ _
  · intro hZ
    have hpre : IsIrreducible (g ⁻¹' (Z : Set E)) := by
      let : IrreducibleSpace (Z : Set E) := Subtype.irreducibleSpace Z.isIrreducible
      exact isIrreducible_iff_irreducibleSpace.mpr
        ((hg.isEmbedding.homeomorphOfSubsetRange hZ).irreducibleSpace_iff.mpr inferInstance)
    refine ⟨⟨g ⁻¹' (Z : Set E), hpre, Z.isClosed.preimage hg.continuous⟩, ?_⟩
    apply TopologicalSpace.IrreducibleCloseds.ext
    rw [TopologicalSpace.IrreducibleCloseds.coe_map_of_isClosedEmbedding hg,
      TopologicalSpace.IrreducibleCloseds.coe_mk, Set.image_preimage_eq_of_subset hZ]

/-- A closed embedding preserves the height of each irreducible closed subset under
the existing map on irreducible closed sets, with their canonical inclusion orders. -/
theorem Topology.IsClosedEmbedding.height_map
    {D : Type w} {E : Type u} [TopologicalSpace D] [TopologicalSpace E]
    {g : D → E} (hg : Topology.IsClosedEmbedding g)
    (Z : TopologicalSpace.IrreducibleCloseds D) :
    Order.height (TopologicalSpace.IrreducibleCloseds.map g hg.continuous Z) =
      Order.height Z := by
  refine (Order.height_eq_of_strictMono _
    (TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing hg.isInducing) ?_ Z).symm
  intro A B hB
  have hsub : (B : Set E) ⊆ Set.range g := by
    refine Set.Subset.trans hB.le ?_
    rw [TopologicalSpace.IrreducibleCloseds.coe_map_of_isClosedEmbedding hg]
    exact Set.image_subset_range _ _
  obtain ⟨B', hB'⟩ : B ∈ Set.range
      (TopologicalSpace.IrreducibleCloseds.map g hg.continuous) := by
    rw [TopologicalSpace.IrreducibleCloseds.range_map_of_isClosedEmbedding hg]
    exact hsub
  refine ⟨B', ?_, hB'⟩
  have hle : B' ≤ A := by
    apply (Set.image_subset_image_iff hg.injective).mp
    simpa only [← TopologicalSpace.IrreducibleCloseds.coe_map_of_isClosedEmbedding hg,
      hB'] using (show (B : Set E) ⊆
        (TopologicalSpace.IrreducibleCloseds.map g hg.continuous A : Set E) from hB.le)
  refine lt_of_le_of_ne hle ?_
  rintro rfl
  exact hB.ne hB'.symm

private theorem topologicalKrullDim_eq_iSup_of_irreducibleCloseds_subset_range
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsClosedEmbedding (f i))
    (hcontain : ∀ Z : TopologicalSpace.IrreducibleCloseds X,
      ∃ i, (Z : Set X) ⊆ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  refine le_antisymm ?_ (iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le)
  calc
    topologicalKrullDim X =
        ⨆ Z : TopologicalSpace.IrreducibleCloseds X, (Order.height Z : WithBot ℕ∞) :=
      Order.krullDim_eq_iSup_height
    _ ≤ ⨆ i, topologicalKrullDim (Y i) := by
      refine iSup_le fun Z => ?_
      obtain ⟨i, hi⟩ := hcontain Z
      obtain ⟨W, hW⟩ : Z ∈ Set.range
          (TopologicalSpace.IrreducibleCloseds.map (f i) (hf i).continuous) := by
        rw [TopologicalSpace.IrreducibleCloseds.range_map_of_isClosedEmbedding (hf i)]
        exact hi
      calc
        (Order.height Z : WithBot ℕ∞) = (Order.height W : WithBot ℕ∞) := by
          rw [← hW, (hf i).height_map]
        _ ≤ topologicalKrullDim (Y i) := Order.height_le_krullDim W
        _ ≤ ⨆ j, topologicalKrullDim (Y j) :=
          le_iSup (fun j : ι => topologicalKrullDim (Y j)) i

/-- A space's topological Krull dimension is the supremum of the dimensions of the domains
of any jointly surjective family of closed embeddings with locally finite images.

Local finiteness is imposed on the original indexed family of images, including repeated
images. The domain spaces retain their given topologies. No separation, sobriety,
Noetherianity, quasi-compactness, finiteness, nonemptiness or dimension bound is assumed.
The supremum is in `WithBot ℕ∞`, including the empty and infinite cases. -/
theorem topologicalKrullDim_eq_iSup_of_isClosedEmbedding_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsClosedEmbedding (f i))
    (hfin : LocallyFinite (fun i => Set.range (f i)))
    (hcov : ∀ x : X, ∃ i, ∃ y : Y i, f i y = x) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  refine topologicalKrullDim_eq_iSup_of_irreducibleCloseds_subset_range f hf fun Z => ?_
  have hcover : (Z : Set X) ⊆ ⋃ i, Set.range (f i) := by
    intro x _
    obtain ⟨i, y, rfl⟩ := hcov x
    exact Set.mem_iUnion.mpr ⟨i, ⟨y, rfl⟩⟩
  exact Z.isIrreducible.exists_subset_of_locallyFinite_isClosed_cover
    (fun i => Set.range (f i)) (fun i => (hf i).isClosed_range) hfin hcover

/-- The topological Krull dimension of a space equals the supremum of the dimensions of
its closed subspaces in a locally finite closed cover.

Each subspace carries the topology induced from the original space. Local finiteness
counts the original indices, including repetitions. The supremum is in `WithBot ℕ∞`,
including the empty and infinite cases. -/
theorem topologicalKrullDim_eq_iSup_of_locallyFinite_isClosed_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hfin : LocallyFinite C) (hcov : ⋃ i, C i = Set.univ) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (C i) := by
  refine topologicalKrullDim_eq_iSup_of_isClosedEmbedding_cover
    (fun i => (Subtype.val : C i → X)) (fun i => (hC i).isClosedEmbedding_subtypeVal) ?_ ?_
  · simpa only [Subtype.range_coe] using hfin
  · intro x
    have hx : x ∈ ⋃ i, C i := by
      rw [hcov]
      trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- The topological Krull dimension of a space is the supremum of the dimensions of
its canonical irreducible components, with their induced subspace topologies.

The supremum is in `WithBot ℕ∞`: the empty space gives `⊥`, and infinite component
families and unbounded dimensions are included without attainment. No local finiteness,
Noetherianity, separation or sobriety assumption is needed. The components and their
closedness are those of Mathlib's `Mathlib.Topology.Irreducible`. -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents
    (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X =
      ⨆ C : irreducibleComponents X, topologicalKrullDim (C : Set X) := by
  refine topologicalKrullDim_eq_iSup_of_irreducibleCloseds_subset_range
    (Y := fun C : irreducibleComponents X => (C : Set X)) (fun _ => Subtype.val)
    (fun C => (isClosed_of_mem_irreducibleComponents C.val C.property).isClosedEmbedding_subtypeVal)
    fun Z => ?_
  obtain ⟨C, hC, hZC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (Z : Set X) Z.isIrreducible
  exact ⟨⟨C, hC⟩, by simpa only [Subtype.range_coe] using hZC⟩
