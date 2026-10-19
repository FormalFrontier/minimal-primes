/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Topology.KrullDimension.OpenCover

/-!
# Open-cover dimension on discrete and empty spaces

The discrete two-point space `Bool` is covered by its two nonempty proper singleton opens.
The dimension equality is applied to this cover, rather than to the one-member whole-space
cover. The empty space with an empty index type gives bottom in `WithBot ℕ∞`.
-/

private def singletonCover (b : Bool) : Set Bool := {b}

private theorem mem_singletonCover (b x : Bool) : x ∈ singletonCover b ↔ x = b := by
  rfl

private theorem singletonCover_isOpen (b : Bool) : IsOpen (singletonCover b) :=
  isOpen_discrete _

private theorem singletonCover_nonempty (b : Bool) : (singletonCover b).Nonempty :=
  ⟨b, (mem_singletonCover b b).2 rfl⟩

private theorem singletonCover_ne_univ (b : Bool) : singletonCover b ≠ Set.univ := by
  intro h
  have hmem : (!b) ∈ singletonCover b := by
    rw [h]
    trivial
  cases b <;> simp [singletonCover] at hmem

private theorem singletonCover_iUnion : (⋃ b : Bool, singletonCover b) = Set.univ := by
  ext x
  simp [singletonCover]

private theorem bool_dimension_open_cover :
    (⋃ b : Bool, singletonCover b) = Set.univ ∧
      (∀ b : Bool, (singletonCover b).Nonempty ∧ singletonCover b ≠ Set.univ) ∧
      topologicalKrullDim Bool = ⨆ b : Bool, topologicalKrullDim (singletonCover b) := by
  refine ⟨singletonCover_iUnion, fun b =>
    ⟨singletonCover_nonempty b, singletonCover_ne_univ b⟩, ?_⟩
  exact topologicalKrullDim_eq_iSup_of_isOpenEmbedding_cover
    (fun b => (Subtype.val : singletonCover b → Bool))
    (fun b => (singletonCover_isOpen b).isOpenEmbedding_subtypeVal)
    (fun x => ⟨x, ⟨x, (mem_singletonCover x x).2 rfl⟩, rfl⟩)

private theorem empty_dimension : topologicalKrullDim Empty = ⊥ := by
  let : IsEmpty (TopologicalSpace.IrreducibleCloseds Empty) := ⟨fun Z => by
    obtain ⟨x, _⟩ := Z.isIrreducible.nonempty
    exact Empty.elim x⟩
  exact Order.krullDim_eq_bot

/-- The empty cover of the empty space has topological Krull dimension bottom. -/
public theorem TopologicalSpace.topologicalKrullDim_empty_index_cover :
    topologicalKrullDim Empty = ⊥ := by
  have hcov : (⋃ i : Empty, (Empty.elim i : Set Empty)) = Set.univ := by
    ext x
    exact Empty.elim x
  simpa only [iSup_of_empty] using
    topologicalKrullDim_eq_iSup_of_isOpen_cover
      (fun i : Empty => (Empty.elim i : Set Empty)) (fun i => Empty.elim i) hcov
