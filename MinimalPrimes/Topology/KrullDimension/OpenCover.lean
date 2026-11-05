/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.KrullDimension
public import MinimalPrimes.Order.KrullDimension

/-!
# Topological Krull dimension under inducing maps and open covers

This module proves that an inducing surjection preserves topological Krull dimension.
The source and target retain their given topologies and have independent universes;
the map need not be injective.

It also proves that the topological Krull dimension of a space is the supremum of the
dimensions of a jointly surjective family of open embeddings into it. The ambient space,
index type and chart
domains have independent universes. In particular, the dimension is the supremum of the
dimensions of the open subspaces in any open cover, with their induced topologies.

For a finite jointly surjective family of inducing maps, it gives an upper bound by
sums of chart dimensions plus the number of selected charts minus one. The supremum
over nonempty subfamilies retains the empty cases. Inducing maps need not be injective,
and the charts need not be open or closed. The characteristic order and range lemmas
strengthen Mathlib's existing `TopologicalSpace.IrreducibleCloseds.map`: mapped inclusion
reflects inclusion, and its range consists of the irreducible closed sets whose
intersection with the map's range is dense in them.

The supremum is taken in `WithBot ℕ∞`. An empty-index cover of the empty space has
dimension `⊥`, not zero. Arbitrary infinite covers and unbounded dimensions are included:
the supremum need not be attained by a member of the cover.

## References

* Mathlib's `Mathlib.Topology.KrullDimension` for topological Krull dimension,
  monotonicity under inducing maps, and open-embedding coheight invariance.
* Mathlib's inducing-map composition and surjective-function section APIs.
* Mathlib's `Mathlib.Order.KrullDimension` for the empty-safe supremum-of-coheights formula.
* Mathlib's `Mathlib.Topology.Sets.Closeds` for the irreducible-closed map, and
  `Mathlib.Topology.Irreducible` for irreducibility and finite closed covers.
* `MinimalPrimes.Order.KrullDimension` for the finite-cover powerset bound.
-/

@[expose] public section

universe u v w

/-- An inducing surjection preserves topological Krull dimension.

Both spaces retain their given topologies. No injectivity, separation, sobriety,
Noetherianity, finiteness or nonemptiness hypothesis is needed. The equality is in
`WithBot ℕ∞`, including the empty and infinite cases. -/
theorem Topology.IsInducing.topologicalKrullDim_eq
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsInducing f) (hsurj : Function.Surjective f) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  refine le_antisymm hf.topologicalKrullDim_le ?_
  have hs : Topology.IsInducing (Function.surjInv hsurj) := by
    apply hf.of_comp_iff.mp
    rw [Function.comp_surjInv]
    exact Topology.IsInducing.id
  exact hs.topologicalKrullDim_le

/-- A space's topological Krull dimension is the supremum of the dimensions of the domains
of any jointly surjective family of open embeddings into it.

The given chart domains and their topologies are retained. No separation, sobriety,
Noetherianity, quasi-compactness, finiteness, nonemptiness or dimension bound is assumed.
The supremum is in `WithBot ℕ∞`, including the empty and infinite cases. -/
theorem topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hcov : ∀ x : X, ∃ i, ∃ y : Y i, f i y = x) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  refine le_antisymm ?_ (iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le)
  calc
    topologicalKrullDim X =
        ⨆ Z : TopologicalSpace.IrreducibleCloseds X, (Order.coheight Z : WithBot ℕ∞) :=
      Order.krullDim_eq_iSup_coheight
    _ ≤ ⨆ i, topologicalKrullDim (Y i) := by
      refine iSup_le fun Z => ?_
      obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
      obtain ⟨i, y, hfy⟩ := hcov x
      have hpre : ((f i) ⁻¹' (Z : Set X)).Nonempty := by
        refine ⟨y, ?_⟩
        simpa only [Set.mem_preimage, hfy] using hx
      let W : TopologicalSpace.IrreducibleCloseds (Y i) :=
        ⟨(f i) ⁻¹' (Z : Set X),
          Z.isIrreducible.preimage (hf i) ⟨x, hx, y, hfy⟩,
          IsClosed.preimage (hf i).continuous Z.isClosed⟩
      have hW : (W : Set (Y i)) = (f i) ⁻¹' (Z : Set X) :=
        TopologicalSpace.IrreducibleCloseds.coe_mk _ _ _
      have hmap : TopologicalSpace.IrreducibleCloseds.map (f i) (hf i).continuous W = Z := by
        apply TopologicalSpace.IrreducibleCloseds.ext
        rw [TopologicalSpace.IrreducibleCloseds.coe_map, hW]
        exact closure_image_preimage_of_isPreirreducible (f i) (hf i).isOpenMap
          (Z : Set X) hpre Z.isIrreducible.isPreirreducible Z.isClosed
      calc
        (Order.coheight Z : WithBot ℕ∞) = (Order.coheight W : WithBot ℕ∞) := by
          rw [← hmap, (hf i).coheight_map]
        _ ≤ topologicalKrullDim (Y i) := Order.coheight_le_krullDim W
        _ ≤ ⨆ j, topologicalKrullDim (Y j) :=
          le_iSup (fun j : ι => topologicalKrullDim (Y j)) i

/-- The topological Krull dimension of a space equals the supremum of the dimensions of
its open subspaces in an arbitrary open cover.

Each open subspace carries the topology induced from the original space. The supremum
is in `WithBot ℕ∞`, including the empty and infinite cases. -/
theorem topologicalKrullDim_eq_iSup_of_isOpen_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i) := by
  refine topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
    (fun i => (Subtype.val : U i → X)) (fun i => (hU i).isOpenEmbedding_subtypeVal) ?_
  intro x
  have hx : x ∈ ⋃ i, U i := by
    rw [hcov]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- An inducing map preserves and reflects irreducibility of any subset, without
requiring point injectivity. -/
theorem Topology.IsInducing.isIrreducible_image
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : Topology.IsInducing f) {s : Set Y} :
    IsIrreducible (f '' s) ↔ IsIrreducible s := by
  constructor
  · intro hs
    refine ⟨Set.image_nonempty.mp hs.nonempty, ?_⟩
    intro U V hU hV hUs hVs
    obtain ⟨U', hU', rfl⟩ := hf.isOpen_iff.mp hU
    obtain ⟨V', hV', rfl⟩ := hf.isOpen_iff.mp hV
    obtain ⟨y, hy, hyU⟩ := hUs
    obtain ⟨z, hz, hzV⟩ := hVs
    obtain ⟨x, ⟨a, ha, rfl⟩, haU, haV⟩ := hs.isPreirreducible U' V' hU' hV'
      ⟨f y, ⟨y, hy, rfl⟩, hyU⟩ ⟨f z, ⟨z, hz, rfl⟩, hzV⟩
    exact ⟨a, ha, haU, haV⟩
  · intro hs
    exact hs.image f hf.continuous.continuousOn

/-- For an inducing map, inclusion between images under the existing map on irreducible
closed sets is equivalent to inclusion in the domain. No point injectivity is required. -/
theorem TopologicalSpace.IrreducibleCloseds.map_le_map_iff_of_isInducing
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : Topology.IsInducing f)
    (A B : TopologicalSpace.IrreducibleCloseds Y) :
    TopologicalSpace.IrreducibleCloseds.map f hf.continuous A ≤
        TopologicalSpace.IrreducibleCloseds.map f hf.continuous B ↔ A ≤ B := by
  constructor
  · intro h
    have hpre := Set.preimage_mono (f := f)
      (show closure (f '' (A : Set Y)) ⊆ closure (f '' (B : Set Y)) from h)
    change (A : Set Y) ⊆ (B : Set Y)
    simpa only [← hf.closure_eq_preimage_closure_image,
      A.isClosed.closure_eq, B.isClosed.closure_eq] using hpre
  · intro h
    exact TopologicalSpace.IrreducibleCloseds.map_mono hf.continuous h

/-- An irreducible closed set belongs to the range of the existing map induced by an
inducing map exactly when its intersection with the point-map range is dense in it.
Closure is taken in the given ambient topology; the domain need not be `T₀`. -/
theorem TopologicalSpace.IrreducibleCloseds.mem_range_map_iff_of_isInducing
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : Topology.IsInducing f)
    (Z : TopologicalSpace.IrreducibleCloseds X) :
    Z ∈ Set.range (TopologicalSpace.IrreducibleCloseds.map f hf.continuous) ↔
      closure ((Z : Set X) ∩ Set.range f) = (Z : Set X) := by
  constructor
  · rintro ⟨W, rfl⟩
    rw [TopologicalSpace.IrreducibleCloseds.coe_map]
    apply le_antisymm
    · exact closure_minimal Set.inter_subset_left isClosed_closure
    · apply closure_mono
      intro x hx
      exact ⟨subset_closure hx, Set.image_subset_range f (W : Set Y) hx⟩
  · intro hZ
    have hirr : IsIrreducible (f '' (f ⁻¹' (Z : Set X))) := by
      rw [Set.image_preimage_eq_inter_range]
      apply isIrreducible_iff_closure.mp
      rw [hZ]
      exact Z.isIrreducible
    let W : TopologicalSpace.IrreducibleCloseds Y :=
      ⟨f ⁻¹' (Z : Set X), hf.isIrreducible_image.mp hirr,
        Z.isClosed.preimage hf.continuous⟩
    refine ⟨W, TopologicalSpace.IrreducibleCloseds.ext ?_⟩
    rw [TopologicalSpace.IrreducibleCloseds.coe_map,
      TopologicalSpace.IrreducibleCloseds.coe_mk, Set.image_preimage_eq_inter_range]
    exact hZ

/-- The topological Krull dimension of a space covered by finitely many inducing maps
is bounded by the supremum over nonempty subfamilies of the sum of their domain
dimensions plus their cardinality minus one.

Only maps at indices in `I` must be inducing. All spaces retain their given topologies;
no injectivity, separation, nonemptiness, finite dimension or attainment is required.
Subtraction takes place in `ℕ` before casting to `WithBot ℕ∞`. The powerset expression
is the finite-cover bound of `Order.krullDim_le_iSup_of_subset_biUnion_finset`. -/
theorem topologicalKrullDim_le_iSup_of_isInducing_finset_cover
    {ι : Type u} {X : Type v} {Y : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
    (I : Finset ι) (f : ∀ i, Y i → X)
    (hf : ∀ i ∈ I, Topology.IsInducing (f i))
    (hcov : ∀ x : X, ∃ i ∈ I, ∃ y : Y i, f i y = x) :
    topologicalKrullDim X ≤
      ⨆ J ∈ I.powerset, ⨆ (_ : J.Nonempty),
        (∑ i ∈ J, topologicalKrullDim (Y i)) + ((J.card - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let s : ι → Set (TopologicalSpace.IrreducibleCloseds X) := fun i =>
    {Z | closure ((Z : Set X) ∩ Set.range (f i)) = (Z : Set X)}
  have hs (i : ι) (hi : i ∈ I) :
      Order.krullDim (s i) = topologicalKrullDim (Y i) := by
    let e := OrderEmbedding.ofMapLEIff
      (TopologicalSpace.IrreducibleCloseds.map (f i) (hf i hi).continuous)
      (TopologicalSpace.IrreducibleCloseds.map_le_map_iff_of_isInducing (hf i hi))
    have hr : Set.range e = s i := by
      ext Z
      exact TopologicalSpace.IrreducibleCloseds.mem_range_map_iff_of_isInducing (hf i hi) Z
    exact (Order.krullDim_eq_of_orderIso
      (e.orderIso.trans (Set.orderIsoOfEq _ _ hr))).symm
  have hcover : (Set.univ : Set (TopologicalSpace.IrreducibleCloseds X)) ⊆
      ⋃ i ∈ I, s i := by
    intro Z _
    let C : ι → Set X := fun i => closure ((Z : Set X) ∩ Set.range (f i))
    have hclosed : ∀ D ∈ I.image C, IsClosed D := by
      intro D hD
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
      exact isClosed_closure
    have hZcover : (Z : Set X) ⊆ ⋃₀ (I.image C : Set (Set X)) := by
      intro x hx
      obtain ⟨i, hi, y, rfl⟩ := hcov x
      exact Set.mem_sUnion.mpr ⟨C i, Finset.mem_image.mpr ⟨i, hi, rfl⟩,
        subset_closure ⟨hx, Set.mem_range_self y⟩⟩
    obtain ⟨D, hD, hZD⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp Z.isIrreducible (I.image C) hclosed hZcover
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hD
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
    exact le_antisymm (closure_minimal Set.inter_subset_left Z.isClosed) hZD
  calc
    topologicalKrullDim X =
        Order.krullDim (Set.univ : Set (TopologicalSpace.IrreducibleCloseds X)) :=
      (Order.krullDim_eq_of_orderIso OrderIso.Set.univ).symm
    _ ≤ ⨆ J ∈ I.powerset, ⨆ (_ : J.Nonempty),
        (∑ i ∈ J, Order.krullDim (s i)) + ((J.card - 1 : ℕ) : WithBot ℕ∞) :=
      Order.krullDim_le_iSup_of_subset_biUnion_finset I s Set.univ hcover
    _ = _ := by
      apply iSup_congr
      intro J
      apply iSup_congr
      intro hJ
      have hsub : J ⊆ I := Finset.mem_powerset.mp hJ
      apply iSup_congr
      intro _
      congr 1
      exact Finset.sum_congr rfl fun i hi => hs i (hsub hi)
