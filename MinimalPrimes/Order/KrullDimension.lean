/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.KrullDimension

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Minimal
import Mathlib.Order.UpperLower.Basic

/-!
# Krull dimension of products and covers, and boundary deletion

In pointwise product preorders, the height and coheight of a pair are the sums of
the coordinate heights and coheights. The order dimension of a binary product is
the sum of the factor dimensions, and a finite dependent product has dimension the
sum of its fibre dimensions. These formulas include empty factors and infinite
dimensions. In `WithBot ℕ∞`, bottom absorbs addition, so an empty factor gives bottom
even when another factor has top dimension. An empty-index product has dimension
zero. These are pointwise order products, not lexicographic or topological products.

The order dimension of an indexed union of upper sets is the supremum of the
dimensions of its pieces. The order-dual statement holds for lower sets. The
pieces retain the ambient preorder, and the index type and carrier have independent
universes. The equalities include empty unions, whose dimension is bottom, and
infinite suprema that are not attained by a piece. They concern order dimension,
not the topological dimension of an arbitrary subspace.

The same supremum formula holds for inclusion-directed unions of arbitrary subsets.
Here too all subtypes inherit the given ambient preorder, with no antisymmetry,
nonemptiness or finite-dimensionality requirement.

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
The product formulas use its finite-chain induction, fixed-coordinate maps and gluing,
height suprema, order equivalences and extended-natural sum formulas.
For directed unions, the finite ambient-value range of each strict series fits in one piece;
restricting those same values preserves its length and the inherited order. This uses the
defining `WithBot ℕ∞` supremum, without a nonemptiness premise or a longest chain.
The directed-family predicate is from `Mathlib.Order.Directed` (Johannes Hölzl and Yaël Dillies),
and finite containment and finite ranges are from `Mathlib.Data.Set.Finite.Lattice` and
`Mathlib.Data.Set.Finite.Range` (Johannes Hölzl, Mario Carneiro and Kyle Miller).
-/

@[expose] public section

universe u v w

open scoped BigOperators

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

/-- The order dimension of an inclusion-directed union is the supremum of the dimensions
of its pieces. All subtypes inherit the given ambient preorder. The formula includes empty
unions, of dimension bottom, and infinite suprema not attained by any piece. -/
theorem Order.krullDim_iUnion_of_directed
    {α : Type u} [Preorder α] {ι : Sort v}
    (s : ι → Set α) (hs : Directed (· ⊆ ·) s) :
    Order.krullDim (⋃ i, s i) = ⨆ i, Order.krullDim (s i) := by
  apply le_antisymm
  · change (⨆ p : LTSeries (⋃ i, s i), (p.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun p ↦ ?_
    -- Capture ambient values, keeping the same series length and inherited order.
    let f : Fin (p.length + 1) → α := fun j ↦ (p j).1
    have hf : (Set.range f).Finite := Set.finite_range f
    have hfU : Set.range f ⊆ ⋃ i, s i := by
      rintro x ⟨j, rfl⟩
      exact (p j).property
    obtain ⟨i₀, _⟩ := Set.mem_iUnion.mp p.head.property
    have hn : (Set.range s).Nonempty := ⟨s i₀, ⟨i₀, rfl⟩⟩
    have hfS : Set.range f ⊆ ⋃₀ Set.range s := by
      simpa only [Set.sUnion_range] using hfU
    obtain ⟨t, ht, hft⟩ :=
      DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
        hn hs.directedOn_range hf hfS
    obtain ⟨i, rfl⟩ := ht
    let q : LTSeries (s i) :=
      LTSeries.mk p.length (fun j ↦ ⟨f j, hft ⟨j, rfl⟩⟩)
        (fun _ _ hjk ↦ p.strictMono hjk)
    have hq : (p.length : WithBot ℕ∞) ≤ Order.krullDim (s i) :=
      Order.LTSeries.length_le_krullDim q
    exact le_iSup_of_le i hq
  · refine iSup_le fun i ↦ ?_
    exact Order.krullDim_le_of_strictMono
      (fun x : s i ↦
        (⟨x.1, Set.mem_iUnion.mpr ⟨i, x.2⟩⟩ : ⋃ j, s j))
      (fun _ _ h ↦ h)

/-- The height of a pair in the pointwise product preorder is the sum of its
coordinate heights, including infinite heights. -/
theorem Order.height_prod
    {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (a : α) (b : β) :
    Order.height (a, b) = Order.height a + Order.height b := by
  apply le_antisymm
  · have hseries (p : LTSeries (α × β)) :
        (p.length : ℕ∞) ≤ Order.height p.last.1 + Order.height p.last.2 := by
      refine RelSeries.inductionOn'
        (motive := fun q : LTSeries (α × β) ↦
          (q.length : ℕ∞) ≤ Order.height q.last.1 + Order.height q.last.2)
        ?_ ?_ p
      · intro x
        simp only [RelSeries.singleton_length, ENat.natCast_zero]
        exact bot_le
      · intro q x hx hq
        simp only [RelSeries.snoc_length, RelSeries.last_snoc,
          ENat.natCast_add, ENat.natCast_one]
        rcases Prod.lt_iff.mp hx with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
        · calc
            (q.length : ℕ∞) + 1 ≤
                (Order.height q.last.1 + Order.height q.last.2) + 1 :=
              add_le_add hq le_rfl
            _ = (Order.height q.last.1 + 1) + Order.height q.last.2 :=
              add_right_comm _ _ _
            _ ≤ Order.height x.1 + Order.height x.2 :=
              add_le_add (Order.height_add_one_le hfst) (Order.height_mono hsnd)
        · calc
            (q.length : ℕ∞) + 1 ≤
                (Order.height q.last.1 + Order.height q.last.2) + 1 :=
              add_le_add hq le_rfl
            _ = Order.height q.last.1 + (Order.height q.last.2 + 1) :=
              add_assoc _ _ _
            _ ≤ Order.height x.1 + Order.height x.2 :=
              add_le_add (Order.height_mono hfst) (Order.height_add_one_le hsnd)
    apply Order.height_le
    intro p hp
    simpa only [hp] using hseries p
  · -- Singleton endpoint chains justify adding the two endpoint suprema, even at top.
    rw [Order.height_eq_iSup_last_eq a, Order.height_eq_iSup_last_eq b]
    refine ENat.biSup_add_biSup_le'
      (p := fun p : LTSeries α ↦ p.last = a)
      (q := fun q : LTSeries β ↦ q.last = b)
      ⟨RelSeries.singleton _ a, rfl⟩ ⟨RelSeries.singleton _ b, rfl⟩ ?_
    intro p hp q hq
    let p' : LTSeries (α × β) :=
      LTSeries.map p (fun x ↦ (x, q.head))
        (fun _ _ h ↦ Prod.mk_lt_mk_iff_left.mpr h)
    let q' : LTSeries (α × β) :=
      LTSeries.map q (fun y ↦ (p.last, y))
        (fun _ _ h ↦ Prod.mk_lt_mk_iff_right.mpr h)
    have hjoin : p'.last = q'.head := rfl
    have h := Order.length_le_height_last (p := p'.smash q' hjoin)
    rw [RelSeries.smash_length, RelSeries.last_smash] at h
    change ((p.length + q.length : ℕ) : ℕ∞) ≤ Order.height (p.last, q.last) at h
    simpa only [Nat.cast_add, hp, hq] using h

/-- The coheight of a pair in the pointwise product preorder is the sum of its
coordinate coheights, including infinite coheights. -/
theorem Order.coheight_prod
    {α : Type u} {β : Type v} [Preorder α] [Preorder β]
    (a : α) (b : β) :
    Order.coheight (a, b) = Order.coheight a + Order.coheight b := by
  change Order.height (α := (α × β)ᵒᵈ) (a, b) =
    Order.height (α := αᵒᵈ) a + Order.height (α := βᵒᵈ) b
  exact (Order.height_orderIso
    (OrderIso.refl _ : (α × β)ᵒᵈ ≃o αᵒᵈ × βᵒᵈ) (a, b)).symm.trans
      (Order.height_prod (α := αᵒᵈ) (β := βᵒᵈ) a b)

/-- The dimension of a pointwise product of preorders is the sum of the factor
dimensions in `WithBot ℕ∞`. An empty factor gives bottom even when the other
factor has infinite dimension. -/
theorem Order.krullDim_prod
    (α : Type u) (β : Type v) [Preorder α] [Preorder β] :
    Order.krullDim (α × β) = Order.krullDim α + Order.krullDim β := by
  cases isEmpty_or_nonempty α with
  | inl h => simp [Order.krullDim_eq_bot]
  | inr h =>
    cases isEmpty_or_nonempty β with
    | inl h => simp [Order.krullDim_eq_bot]
    | inr h =>
      rw [Order.krullDim_eq_iSup_height_of_nonempty (α := α × β),
        Order.krullDim_eq_iSup_height_of_nonempty (α := α),
        Order.krullDim_eq_iSup_height_of_nonempty (α := β),
        ← WithBot.coe_add, WithBot.coe_inj, iSup_prod]
      simp_rw [Order.height_prod, ← ENat.add_iSup, ← ENat.iSup_add]

/-- The dimension of a finite dependent pointwise product is the sum of its fibre
dimensions in `WithBot ℕ∞`. Empty factors give bottom, and an empty index gives
zero. No fibre is required to be nonempty or finite-dimensional. -/
theorem Order.krullDim_pi
    {ι : Type w} [Fintype ι]
    (α : ι → Type v) [∀ i, Preorder (α i)] :
    Order.krullDim (∀ i, α i) = ∑ i, Order.krullDim (α i) := by
  have hfin :
      ∀ (n : ℕ) (β : Fin n → Type v) [∀ i, Preorder (β i)],
        Order.krullDim (∀ i, β i) = ∑ i, Order.krullDim (β i) := by
    intro n
    induction n with
    | zero =>
      intro β hβ
      simpa only [Fin.sum_univ_zero] using
        (Order.krullDim_eq_zero_of_unique (α := ∀ i : Fin 0, β i))
    | succ n ih =>
      intro β hβ
      rw [Order.krullDim_eq_of_orderIso (Fin.consOrderIso β).symm,
        Order.krullDim_prod, ih (fun i : Fin n ↦ β i.succ),
        Fin.sum_univ_succ]
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  calc
    Order.krullDim (∀ i, α i) =
        Order.krullDim (∀ j : Fin (Fintype.card ι), α (e j)) :=
      Order.krullDim_eq_of_orderIso
        { toEquiv := (Equiv.piCongrLeft α e).symm
          map_rel_iff' := by
            intro f g
            change (∀ j, f (e j) ≤ g (e j)) ↔ ∀ i, f i ≤ g i
            exact e.forall_congr_right (q := fun i ↦ f i ≤ g i) }
    _ = ∑ j : Fin (Fintype.card ι), Order.krullDim (α (e j)) :=
      hfin _ _
    _ = ∑ i, Order.krullDim (α i) :=
      e.sum_comp (fun i ↦ Order.krullDim (α i))
