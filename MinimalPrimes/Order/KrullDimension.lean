/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.KrullDimension

import Mathlib.Data.Set.Lattice.Order
import Mathlib.Order.Minimal
import Mathlib.Order.UpperLower.Basic

/-!
# Krull dimension, order covers, and boundary deletion

The order dimension of an indexed union of upper sets is the supremum of the
dimensions of its pieces. The order-dual statement holds for lower sets. The
pieces retain the ambient preorder, and the index type and carrier have independent
universes. The equalities include empty unions, whose dimension is bottom, and
infinite suprema that are not attained by a piece. They concern order dimension,
not the topological dimension of an arbitrary subspace.

For any preorder, the dimension of its nonminimal or nonmaximal locus, plus one,
is at most the ambient dimension. The dimension of the original interior, plus
two, is also at most the ambient dimension. These inequalities take values in
`WithBot ℕ∞`, with no finite-dimensionality or nonemptiness hypothesis. Addition
by a finite number leaves bottom at bottom and top at top.

For any natural number `n`, dimension at most `n + 1` is equivalent to
dimension at most `n` on the subtype of nonminimal points. Order duality gives the
nonmaximal version. Deleting both original boundaries characterizes dimension at
most `n + 2` by dimension at most `n` on the original interior.

All minimality and maximality predicates refer to the given ambient preorder, and
all subtypes carry its inherited order. The nonminimal locus is upward closed by
`IsMin.mono`, so maximality there agrees with ambient maximality. This agreement
identifies the successive deletions with the subtype of points that are neither
minimal nor maximal in the original preorder.

Neither the inequalities nor the finite-bound equivalences assert unconditional
exact dimension subtraction or strict decrease. Empty preorders and antichains are
included: deletion can give an empty subtype, whose Krull dimension is bottom.

In dimension at most two, comparable elements are equivalent in the preorder if the
lower element is not minimal and the upper element is not maximal. The conclusion
is a reverse inequality; equality requires antisymmetry.

## References

Mathlib's `Order.KrullDimension` supplies the dimension bound, order-dual invariance,
height and coheight, and their relations to `IsMin` and `IsMax`. Its `Order.RelSeries`
provides finite strict chains; `Order.Max` supplies the ambient boundary predicates.
The full dimension inequalities use the finite-bound characterizations together
with Mathlib's bottom, zero- and one-dimensional criteria and extended-natural arithmetic.
The cover equalities use its height and coheight restriction and indexed-supremum formulas.
-/

@[expose] public section

universe u v

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

/-- The dimension of the inherited nonminimal locus, plus one in `WithBot ℕ∞`, is at
most the ambient dimension. Minimality is tested in the original preorder. -/
theorem Order.krullDim_not_isMin_add_one_le
    {α : Type u} [Preorder α] :
    Order.krullDim {x : α // ¬ _root_.IsMin x} + 1 ≤ Order.krullDim α := by
  cases hdim : Order.krullDim α with
  | bot =>
    have : IsEmpty α := Order.krullDim_eq_bot_iff.mp hdim
    simp [Order.krullDim_eq_bot]
  | coe d =>
    cases d with
    | top => exact le_top
    | coe n =>
      cases n with
      | zero =>
        -- Dimension zero forces the deletion locus to be empty, not just dimension zero.
        have hmin := Order.krullDim_nonpos_iff_forall_isMin.mp hdim.le
        have : IsEmpty {x : α // ¬ _root_.IsMin x} :=
          ⟨fun x ↦ x.property (hmin x)⟩
        simp [Order.krullDim_eq_bot]
      | succ n =>
        have hbound : Order.KrullDimLE (n + 1) α :=
          (Order.krullDimLE_iff (n + 1) _).mpr hdim.le
        have hdel := (Order.krullDimLE_succ_iff_not_isMin (α := α) n).mp hbound
        have hle := (Order.krullDimLE_iff n _).mp hdel
        simpa only [Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_natCast,
          WithBot.coe_one] using add_le_add_left hle (1 : WithBot ℕ∞)

/-- The dimension of the inherited nonmaximal locus, plus one in `WithBot ℕ∞`, is at
most the ambient dimension. Maximality is tested in the original preorder. -/
theorem Order.krullDim_not_isMax_add_one_le
    {α : Type u} [Preorder α] :
    Order.krullDim {x : α // ¬ _root_.IsMax x} + 1 ≤ Order.krullDim α := by
  have h := Order.krullDim_not_isMin_add_one_le (α := αᵒᵈ)
  change Order.krullDim ({x : α // ¬ _root_.IsMax x})ᵒᵈ + 1 ≤
    Order.krullDim αᵒᵈ at h
  simpa only [Order.krullDim_orderDual] using h

/-- The dimension of the inherited original interior, plus two in `WithBot ℕ∞`, is
at most the ambient dimension. Both extrema are tested in the original preorder. -/
theorem Order.krullDim_not_isMin_not_isMax_add_two_le
    {α : Type u} [Preorder α] :
    Order.krullDim {x : α // ¬ _root_.IsMin x ∧ ¬ _root_.IsMax x} + 2 ≤
      Order.krullDim α := by
  have hlow (h : Order.krullDim α ≤ 1) :
      Order.krullDim {x : α // ¬ _root_.IsMin x ∧ ¬ _root_.IsMax x} = ⊥ := by
    have : IsEmpty {x : α // ¬ _root_.IsMin x ∧ ¬ _root_.IsMax x} :=
      ⟨fun x ↦ (Order.krullDim_le_one_iff.mp h x).elim x.property.1 x.property.2⟩
    exact Order.krullDim_eq_bot
  cases hdim : Order.krullDim α with
  | bot =>
    have : IsEmpty α := Order.krullDim_eq_bot_iff.mp hdim
    simp [Order.krullDim_eq_bot]
  | coe d =>
    cases d with
    | top => exact le_top
    | coe n =>
      rcases n with _ | _ | n
      · simp [hlow (by simp [hdim])]
      · simp [hlow (by simp [hdim])]
      · have hbound : Order.KrullDimLE (n + 2) α :=
          (Order.krullDimLE_iff (n + 2) _).mpr hdim.le
        have hdel :=
          (Order.krullDimLE_add_two_iff_not_isMin_not_isMax (α := α) n).mp hbound
        have hle := (Order.krullDimLE_iff n _).mp hdel
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, WithBot.coe_add,
          WithBot.coe_natCast, WithBot.coe_one, WithBot.coe_ofNat, add_assoc,
          one_add_one_eq_two] using
          add_le_add_left hle (2 : WithBot ℕ∞)

/-- The order dimension of an indexed union of upper sets is the supremum of their
order dimensions, including empty unions and infinite suprema. Every subtype has
its inherited ambient order. -/
theorem Order.krullDim_iUnion_of_isUpperSet
    {α : Type u} [Preorder α] {ι : Sort v}
    (s : ι → Set α) (hs : ∀ i, IsUpperSet (s i)) :
    Order.krullDim (⋃ i, s i) = ⨆ i, Order.krullDim (s i) := by
  have hdim (t : Set α) (ht : IsUpperSet t) :
      Order.krullDim t = ⨆ x : t, (Order.coheight (x : α) : WithBot ℕ∞) := by
    rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_congr
    intro x
    exact congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞))
      (Order.coheight_eq_of_strictMono (fun y : t ↦ (y : α)) (fun _ _ h ↦ h)
        (by
          intro a b hab
          exact ⟨⟨b, ht hab.le a.property⟩, hab, rfl⟩) x)
  calc
    Order.krullDim (⋃ i, s i) =
        ⨆ x ∈ ⋃ i, s i, (Order.coheight x : WithBot ℕ∞) := by
      rw [hdim _ (isUpperSet_iUnion hs)]
      exact iSup_subtype'' _ (fun x ↦ (Order.coheight x : WithBot ℕ∞))
    _ = ⨆ i, ⨆ x ∈ s i, (Order.coheight x : WithBot ℕ∞) := iSup_iUnion s _
    _ = ⨆ i, Order.krullDim (s i) := by
      apply iSup_congr
      intro i
      rw [hdim _ (hs i)]
      exact (iSup_subtype'' _ (fun x ↦ (Order.coheight x : WithBot ℕ∞))).symm

/-- The order-dual union formula: the order dimension of an indexed union of lower
sets is the supremum of their order dimensions. No piece, index, or ambient point
is required to exist. -/
theorem Order.krullDim_iUnion_of_isLowerSet
    {α : Type u} [Preorder α] {ι : Sort v}
    (s : ι → Set α) (hs : ∀ i, IsLowerSet (s i)) :
    Order.krullDim (⋃ i, s i) = ⨆ i, Order.krullDim (s i) := by
  have h := Order.krullDim_iUnion_of_isUpperSet (α := αᵒᵈ) s
    (fun i ↦ (hs i).toDual)
  change Order.krullDim ({x : α // x ∈ ⋃ i, s i})ᵒᵈ =
    ⨆ i, Order.krullDim ({x : α // x ∈ s i})ᵒᵈ at h
  simpa only [Order.krullDim_orderDual] using h
