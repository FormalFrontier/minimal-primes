/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.KrullDimension

/-!
# Comparison in dimension at most two

In a preorder of Krull dimension at most two, comparable elements are equivalent
in the preorder if the lower element is not minimal and the upper element is not maximal.
The conclusion is a reverse inequality; equality requires antisymmetry.

## References

Mathlib's `Order.KrullDimension` supplies the dimension bound, height and coheight,
and their relations to the predicates `IsMin` and `IsMax`.
-/

@[expose] public section

universe u

/-- In dimension at most two, a comparison from a nonminimal element to a nonmaximal
element also holds in the reverse direction. -/
theorem Order.KrullDimLE.le_of_le_of_not_isMin_of_not_isMax
    {α : Type u} [Preorder α] [Order.KrullDimLE 2 α] {x y : α}
    (hxy : x ≤ y) (hx : ¬ _root_.IsMin x) (hy : ¬ _root_.IsMax y) : y ≤ x := by
  by_contra hyx
  obtain ⟨w, hw⟩ := not_isMin_iff.mp hx
  obtain ⟨z, hz⟩ := not_isMax_iff.mp hy
  have hxy' : x < y := lt_of_le_not_ge hxy hyx
  let c : LTSeries α :=
    (((RelSeries.singleton _ w).snoc x (by simpa using hw)).snoc y
      (by simpa using hxy')).snoc z (by simpa using hz)
  have hlength : c.length ≤ 2 := ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp
    ((Order.LTSeries.length_le_krullDim c).trans
      (Order.KrullDimLE.krullDim_le (n := 2) (α := α))))
  simp [c] at hlength
