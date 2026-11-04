/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.KrullDimension

import Mathlib.Order.Minimal

/-!
# Finite dimension bounds and boundary deletion

For any preorder and natural number `n`, dimension at most `n + 1` is equivalent to
dimension at most `n` on the subtype of nonminimal points. Order duality gives the
nonmaximal version. Deleting both original boundaries characterizes dimension at
most `n + 2` by dimension at most `n` on the original interior.

All minimality and maximality predicates refer to the given ambient preorder, and
all subtypes carry its inherited order. The nonminimal locus is upward closed by
`IsMin.mono`, so maximality there agrees with ambient maximality. This agreement
identifies the successive deletions with the subtype of points that are neither
minimal nor maximal in the original preorder.

These are finite-bound equivalences, not unconditional exact dimension subtraction.
Empty preorders and antichains are included: deletion can give an empty subtype,
whose Krull dimension is bottom.

In dimension at most two, comparable elements are equivalent in the preorder if the
lower element is not minimal and the upper element is not maximal. The conclusion
is a reverse inequality; equality requires antisymmetry.

## References

Mathlib's `Order.KrullDimension` supplies the dimension bound, order-dual invariance,
height and coheight, and their relations to `IsMin` and `IsMax`. Its `Order.RelSeries`
provides finite strict chains; `Order.Max` supplies the ambient boundary predicates.
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

/-- A preorder has dimension at most `n + 1` exactly when its inherited subtype of
nonminimal points has dimension at most `n`. Minimality is tested in the ambient preorder. -/
theorem Order.krullDimLE_succ_iff_not_isMin
    {α : Type u} [Preorder α] (n : ℕ) :
    Order.KrullDimLE (n + 1) α ↔
      Order.KrullDimLE n {x : α // ¬ _root_.IsMin x} := by
  have bound_iff (β : Type u) [Preorder β] (k : ℕ) :
      Order.KrullDimLE k β ↔ ∀ p : LTSeries β, p.length ≤ k := by
    rw [Order.krullDimLE_iff, Order.krullDim, iSup_le_iff]
    constructor
    · intro h p
      exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp (h p))
    · intro h p
      exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (h p))
  rw [bound_iff, bound_iff]
  constructor
  · intro h p
    obtain ⟨x, hx⟩ := not_isMin_iff.mp p.head.property
    let q : LTSeries α :=
      (LTSeries.map p Subtype.val (fun _ _ h ↦ h)).cons x hx
    have hq := h q
    change 0 + p.length + 1 ≤ n + 1 at hq
    lia
  · intro h p
    by_cases hp : p.length = 0
    · simp [hp]
    · -- Every point of the tail lies strictly above the original head.
      have htail (i : Fin ((p.tail hp).length + 1)) :
          ¬ _root_.IsMin (p.tail hp i) := by
        apply not_isMin_of_lt (b := p.head)
        apply p.strictMono
        change 0 < i.val + 1
        exact Nat.succ_pos _
      let q : LTSeries {x : α // ¬ _root_.IsMin x} :=
        LTSeries.mk (p.tail hp).length (fun i ↦ ⟨p.tail hp i, htail i⟩)
          (fun _ _ hij ↦ LTSeries.strictMono (p.tail hp) hij)
      have hq := h q
      change p.length - 1 ≤ n at hq
      lia

/-- The order-dual boundary characterization: a preorder has dimension at most `n + 1`
exactly when its inherited subtype of ambient nonmaximal points has dimension at most `n`. -/
theorem Order.krullDimLE_succ_iff_not_isMax
    {α : Type u} [Preorder α] (n : ℕ) :
    Order.KrullDimLE (n + 1) α ↔
      Order.KrullDimLE n {x : α // ¬ _root_.IsMax x} := by
  have h := Order.krullDimLE_succ_iff_not_isMin (α := αᵒᵈ) n
  rw [Order.krullDimLE_iff, Order.krullDimLE_iff] at h ⊢
  change Order.krullDim αᵒᵈ ≤ ↑(n + 1) ↔
    Order.krullDim ({x : α // ¬ _root_.IsMax x})ᵒᵈ ≤ ↑n at h
  simpa only [Order.krullDim_orderDual] using h

/-- A preorder has dimension at most `n + 2` exactly when its inherited original interior
has dimension at most `n`. Both boundary predicates refer to the ambient preorder. -/
theorem Order.krullDimLE_add_two_iff_not_isMin_not_isMax
    {α : Type u} [Preorder α] (n : ℕ) :
    Order.KrullDimLE (n + 2) α ↔
      Order.KrullDimLE n {x : α // ¬ _root_.IsMin x ∧ ¬ _root_.IsMax x} := by
  let β := {x : α // ¬ _root_.IsMin x}
  have hmax (x : β) : _root_.IsMax x ↔ _root_.IsMax (x : α) := by
    rw [← maximal_true, maximal_true_subtype,
      maximal_iff_isMax (P := fun x : α ↦ ¬ _root_.IsMin x)
        (fun {_ _} hy hyx hx ↦ hy (hx.mono hyx))]
    exact and_iff_right x.property
  let e : {x : β // ¬ _root_.IsMax x} ≃o
      {x : α // ¬ _root_.IsMin x ∧ ¬ _root_.IsMax x} :=
    { toEquiv :=
        (Equiv.subtypeEquivRight (fun x : β ↦ not_congr (hmax x))).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun x : α ↦ ¬ _root_.IsMin x) (fun x : α ↦ ¬ _root_.IsMax x))
      map_rel_iff' := Iff.rfl }
  refine (Order.krullDimLE_succ_iff_not_isMin (α := α) (n + 1)).trans ?_
  refine (Order.krullDimLE_succ_iff_not_isMax (α := β) n).trans ?_
  simp only [Order.krullDimLE_iff, Order.krullDim_eq_of_orderIso e]
