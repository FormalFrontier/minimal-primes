/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.KrullDimension
public import MinimalPrimes.Order.KrullDimension
public import MinimalPrimes.Topology.IrreducibleCloseds

/-!
# Topological Krull dimension of products

The topological Krull dimension of a binary product is the sum of the factor dimensions.
The dimension of an ordinary finite dependent product is the sum of the fibre dimensions.
The binary factors may have independent universes, and all spaces retain their given
topologies and the canonical product topologies.

These equalities lie in `WithBot ℕ∞`. An empty factor gives bottom, including against
infinite dimension; an empty index gives zero. No separation, sobriety, nonemptiness,
Noetherianity, dimension bound or attainment hypothesis is required. There is no
arbitrary-infinite-index sum assertion.

## References

* Mathlib's topological Krull dimension, by Jujian Zhang, Fangming Li and
  Alessandro D'Angelo, defined using the inclusion order on irreducible closed subsets.
* `MinimalPrimes.Topology.IrreducibleCloseds` for the projection-closure order isomorphisms.
* `MinimalPrimes.Order.KrullDimension` for the binary and finite dependent pointwise
  product dimension formulas, together with Mathlib's order-isomorphism invariance.
-/

@[expose] public section

universe u v w

/-- The topological Krull dimension of the canonical binary product is the sum of the
factor dimensions in `WithBot ℕ∞`.

The two spaces retain their given topologies and may have independent universes.
Empty factors, infinite dimensions and nonattainment are included. -/
theorem topologicalKrullDim_prod (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :
    topologicalKrullDim (X × Y) = topologicalKrullDim X + topologicalKrullDim Y := by
  exact (Order.krullDim_eq_of_orderIso
    (TopologicalSpace.IrreducibleCloseds.prodOrderIso X Y)).trans
      (Order.krullDim_prod _ _)

/-- The topological Krull dimension of an ordinary finite dependent product is the sum
of the fibre dimensions in `WithBot ℕ∞`.

Only the index is finite. Each fibre keeps its given topology, and the product has the
canonical product topology. Empty index, empty factors and infinite dimensions are included. -/
theorem topologicalKrullDim_pi {ι : Type w} [Fintype ι]
    (Y : ι → Type u) [∀ i, TopologicalSpace (Y i)] :
    topologicalKrullDim (∀ i, Y i) = ∑ i, topologicalKrullDim (Y i) := by
  exact (Order.krullDim_eq_of_orderIso
    (TopologicalSpace.IrreducibleCloseds.piOrderIso Y)).trans
      (Order.krullDim_pi _)
