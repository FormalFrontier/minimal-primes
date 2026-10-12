/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Order.Monotone.Basic

/-!
# Well-founded lower intervals at finite height

The strict order on the lower interval of an element of finite order-theoretic height is
well-founded. Only that element is required to have finite height; the ambient preorder need
not have finite Krull dimension or well-founded strict order.

For partial orders, restricting an antitone sequence to the lower interval of its initial
element lets the well-founded antitone chain condition give eventual constancy.

## References

The height and well-foundedness APIs are from Mathlib: `Order.height`, `Order.height_mono`,
`Order.height_strictMono`, and `StrictMono.wellFoundedLT`. The height takes values in `ENat`,
whose strict order is well-founded. Eventual constancy in partial orders uses Mathlib's
`WellFoundedLT.antitone_chain_condition`.
-/

@[expose] public section

universe u

namespace Order

/-- The strict order on the lower interval of an element of finite height is well-founded.
No finite-dimensionality or well-foundedness of the ambient preorder is required. -/
theorem wellFoundedLT_Iic_of_height_lt_top
    {α : Type u} [Preorder α] (x : α) (hfin : height x < ⊤) :
    WellFoundedLT (Set.Iic x) := by
  have hheight : StrictMono (fun y : Set.Iic x => height (y : α)) := by
    intro y z hyz
    exact height_strictMono (α := α) hyz
      (lt_of_le_of_lt (height_mono y.property) hfin)
  exact hheight.wellFoundedLT

end Order
