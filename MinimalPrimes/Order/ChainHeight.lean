/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Directed
public import Mathlib.Order.Height
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Chain heights of lexicographic products, sums and directed unions

`Set.chainHeight` is the supremum in `ENat` of the cardinalities of subsets whose distinct
points are pairwise comparable for a given relation. It counts vertices, not steps, dimensions
or ordinal ranks. Pairwise comparability does not imply transitivity or a linear ordering by the
relation.

For the relation `Prod.Lex rα rβ`, comparison uses `rα` in the first coordinate or equality of
first coordinates together with `rβ` in the second. The chain height of a product of sets is the
product of their chain heights when `rα` is irreflexive on the first set. No condition is required
on `rβ`, which may have loops. Loops of `rα` outside the first set are irrelevant.

For `Sum.Lex rα rβ`, comparison within each tag uses the corresponding factor relation, and
every left-tagged point precedes every right-tagged point. The chain height of the union of the
two tagged images is the sum of the factor chain heights, with no relation laws required. In
particular, loops and directed cycles are allowed in either factor. Unlike the product formula,
the sum formula needs no first-irreflexivity hypothesis.

Transport by `toLex` gives the corresponding formulas for the canonical less-than relations on
`α ×ₗ β` and `α ⊕ₗ β`. The sum formula requires only the given less-than structures; the product
formula additionally requires first irreflexivity. Neither formula requires antisymmetry or
transitivity. The two factor types may lie in independent universes.

Empty sets have chain height zero. Thus empty factors are absorbing for the product, including
`0 * ⊤ = 0 = ⊤ * 0`, but contribute zero to the sum. A singleton has height one for any relation,
so two singleton blocks have lexicographic-sum height two. More generally, two nonempty
antichains have lexicographic-sum height two, whereas their disjoint sum under `Sum.LiftRel`
has height one. The ordinary less-than instance on `α ⊕ β` uses this disjoint relation, not
`Sum.Lex`.

A height of `⊤` can arise from unbounded finite chain cardinalities without an infinite chain
or a longest chain. For example, disjoint finite total chains of all positive finite sizes have
height `⊤`, although each chain is finite. Appending a singleton block lexicographically still
leaves every chain finite and gives height `⊤ + 1 = ⊤`. These are ENat cardinality formulas, not
ordinal-addition or Krull-dimension formulas.

For an inclusion-directed family of sets, the chain height of the union is the supremum of
its pieces' chain heights. The relation is arbitrary, and the index may be any sort, including
an empty one; in that case both sides are zero.

## Proof strategy

Products of comparable subsets give the lower bound by cardinal multiplication and ENat suprema.
For the upper bound, take a finite comparable subset, project to the first coordinate and count
its fibres. The first projection is a comparable subset, and local first irreflexivity makes
each fibre a comparable subset for the second relation. This argument never sorts a chain or
assumes either relation is transitive.

For sums, the two tagged slices of a comparable subset are comparable for the respective factor
relations. Their tagged images partition the subset, so their cardinalities add. Conversely,
the tagged union of two factor chains is a chain because every cross pair compares. Taking the
two suprema gives the addition formula without choosing a longest or infinite chain.

For directed unions, every finite positive chain-cardinality witness fits in one piece.
A point of the witness supplies the local nonempty range needed by the finite-containment
theorem; the zero bound requires no index. Testing all natural lower bounds also handles top.

## References

The proof uses Mathlib's chain-height and finite-witness API in `Mathlib.Order.Height`
(Andrew Yang and Vlad Tsyrklevich), relation embeddings in `Mathlib.Order.RelIso.Basic`
(Mario Carneiro and contributors), finite-union cardinality bounds in
`Mathlib.Data.Set.Card.Arithmetic` (Pim Otte), and its set-cardinality, lexicographic product
and ENat supremum APIs. The sum formula uses the sum relation API in Lean's `Init.Data.Sum.Basic`
(Mario Carneiro and Yury G. Kudryashov), the canonical lexicographic sum and relation isomorphism
in `Mathlib.Data.Sum.Order` (Yaël Dillies), and Mathlib's tagged-set partition and
disjoint-cardinality addition APIs. The directed-family predicate is from `Mathlib.Order.Directed`
(Johannes Hölzl and Yaël Dillies). Finite containment in directed unions uses
`Mathlib.Data.Set.Finite.Lattice` (Johannes Hölzl, Mario Carneiro and Kyle Miller).
-/

@[expose] public section

universe u v

namespace Set

/-- The chain height of an inclusion-directed union is the supremum of the chain heights
of its pieces. The relation need not be transitive or irreflexive, and the index may be empty. -/
theorem chainHeight_iUnion_of_directed
    {α : Type u} {ι : Sort v}
    (s : ι → Set α) (r : α → α → Prop)
    (hs : Directed (· ⊆ ·) s) :
    (⋃ i, s i).chainHeight r = ⨆ i, (s i).chainHeight r := by
  apply le_antisymm
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
    cases n with
    | zero => exact bot_le
    | succ n =>
      obtain ⟨t, hts, hcard, htchain⟩ :=
        Set.exists_isChain_of_le_chainHeight (n + 1) hn
      have htfin : t.Finite := Set.finite_of_encard_eq_coe hcard
      have htne : t.Nonempty := Set.encard_pos.mp (by
        rw [hcard]
        exact ENat.natCast_lt_natCast.mpr (Nat.succ_pos n))
      -- A positive witness supplies an index without a global inhabitation assumption.
      obtain ⟨x, hx⟩ := htne
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hts hx)
      have hrange : (Set.range s).Nonempty := ⟨s i, ⟨i, rfl⟩⟩
      obtain ⟨a, ⟨j, rfl⟩, hta⟩ :=
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
          hrange hs.directedOn_range htfin (by rwa [Set.sUnion_range])
      calc
        ((n + 1 : ℕ) : ENat) = t.encard := hcard.symm
        _ ≤ (s j).chainHeight r :=
          Set.encard_le_chainHeight_of_isChain (s j) t hta htchain
        _ ≤ ⨆ i, (s i).chainHeight r :=
          le_iSup (fun i ↦ (s i).chainHeight r) j
  · refine iSup_le fun i ↦ ?_
    exact Set.chainHeight_mono r (s i) (⋃ i, s i) (Set.subset_iUnion s i)

/-- Chain heights multiply for the lexicographic product of two sets when the first relation
is irreflexive on the first set. Neither relation needs to be transitive, and the second relation
need not be irreflexive. -/
theorem chainHeight_prod_lex
    {α : Type u} {β : Type v} (rα : α → α → Prop) (rβ : β → β → Prop)
    (s : Set α) (t : Set β) (hs : ∀ a ∈ s, ¬ rα a a) :
    (s ×ˢ t).chainHeight (Prod.Lex rα rβ) = s.chainHeight rα * t.chainHeight rβ := by
  have hupper :
      (s ×ˢ t).chainHeight (Prod.Lex rα rβ) ≤
        s.chainHeight rα * t.chainHeight rβ := by
    classical
    refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    obtain ⟨c, hcs, hcn, hc⟩ :=
      Set.exists_isChain_of_le_chainHeight n hn
    have hfin : c.Finite := Set.finite_of_encard_eq_coe hcn
    have hfstsub : Prod.fst '' c ⊆ s := by
      rintro _ ⟨p, hp, rfl⟩
      exact (hcs hp).1
    have hfst : IsChain rα (Prod.fst '' c) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
      rcases hc hp hq (fun h => hpq (congrArg Prod.fst h)) with h | h
      · rcases Prod.lex_iff.mp h with h | ⟨h, _⟩
        · exact Or.inl h
        · exact (hpq h).elim
      · rcases Prod.lex_iff.mp h with h | ⟨h, _⟩
        · exact Or.inr h
        · exact (hpq h.symm).elim
    let A : Finset α := (hfin.image Prod.fst).toFinset
    have hA : (A : Set α) = Prod.fst '' c :=
      (hfin.image Prod.fst).coe_toFinset
    have hAbound : (A.card : ENat) ≤ s.chainHeight rα := by
      rw [← Set.encard_coe_eq_coe_finsetCard A, hA]
      exact Set.encard_le_chainHeight_of_isChain s _ hfstsub hfst
    let B : α → Set β := fun a => Prod.mk a ⁻¹' c
    have hfib : ∀ a ∈ A, (B a).encard ≤ t.chainHeight rβ := by
      intro a ha
      have has : a ∈ s := by
        apply hfstsub
        rw [← hA]
        exact ha
      refine Set.encard_le_chainHeight_of_isChain t (B a) ?_ ?_
      · intro b hb
        exact (hcs hb).2
      · exact hc.preimage_relEmbedding
          (RelEmbedding.prodLexMkLeft rβ (hs a has))
    have hcover : c ⊆ ⋃ a ∈ A, ({a} : Set α) ×ˢ B a := by
      rintro ⟨a, b⟩ hp
      refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · change a ∈ (A : Set α)
        rw [hA]
        exact ⟨(a, b), hp, rfl⟩
      · exact ⟨rfl, hp⟩
    calc
      (n : ENat) = c.encard := hcn.symm
      _ ≤ (⋃ a ∈ A, ({a} : Set α) ×ˢ B a).encard :=
        Set.encard_le_encard hcover
      _ ≤ ∑ a ∈ A, (({a} : Set α) ×ˢ B a).encard :=
        A.set_encard_biUnion_le _
      _ = ∑ a ∈ A, (B a).encard := by
        simp only [Set.encard_prod, Set.encard_singleton, one_mul]
      _ ≤ ∑ _a ∈ A, t.chainHeight rβ := Finset.sum_le_sum hfib
      _ = (A.card : ENat) * t.chainHeight rβ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ s.chainHeight rα * t.chainHeight rβ :=
        mul_le_mul_of_nonneg_right hAbound zero_le
  have hlower :
      s.chainHeight rα * t.chainHeight rβ ≤
        (s ×ˢ t).chainHeight (Prod.Lex rα rβ) := by
    classical
    rw [Set.chainHeight_eq_iSup s rα, ENat.iSup_mul]
    refine iSup_le fun c => ?_
    rw [Set.chainHeight_eq_iSup t rβ, ENat.mul_iSup]
    refine iSup_le fun d => ?_
    rw [← Set.encard_prod]
    apply Set.encard_le_chainHeight_of_isChain (s ×ˢ t) (c.1 ×ˢ d.1)
      (Set.prod_mono c.2.1 d.2.1)
    intro x hx y hy hxy
    by_cases h : x.1 = y.1
    · have hsnd : x.2 ≠ y.2 := fun h' => hxy (Prod.ext h h')
      rcases d.2.2 hx.2 hy.2 hsnd with h' | h'
      · exact Or.inl (Prod.lex_iff.mpr (Or.inr ⟨h, h'⟩))
      · exact Or.inr (Prod.lex_iff.mpr (Or.inr ⟨h.symm, h'⟩))
    · rcases c.2.2 hx.1 hy.1 h with h' | h'
      · exact Or.inl (Prod.lex_iff.mpr (Or.inl h'))
      · exact Or.inr (Prod.lex_iff.mpr (Or.inl h'))
  exact le_antisymm hupper hlower

/-- Chain heights multiply for the image of a set product in the lexicographic type synonym,
with the canonical less-than relation and an irreflexive first less-than relation. The second
less-than relation may have loops; no transitivity is required in either factor. The first
irreflexivity instance is automatic for preorders. -/
theorem chainHeight_toLex_prod
    {α : Type u} {β : Type v} [LT α] [LT β]
    [Std.Irrefl ((· < ·) : α → α → Prop)] (s : Set α) (t : Set β) :
    ((toLex : α × β → α ×ₗ β) '' (s ×ˢ t)).chainHeight
        (fun x y : α ×ₗ β => x < y) =
      s.chainHeight (fun x y : α => x < y) *
        t.chainHeight (fun x y : β => x < y) := by
  calc
    _ = (s ×ˢ t).chainHeight (Prod.Lex (fun x y : α => x < y)
        (fun x y : β => x < y)) :=
      chainHeight_eq_of_relIso (s ×ˢ t)
        (RelIso.ofOnFun (fun x y : α ×ₗ β => x < y) toLex)
    _ = _ := chainHeight_prod_lex _ _ s t (fun a _ => irrefl a)

/-- Chain heights add for the union of the two tagged images under the lexicographic sum
relation. The relations are arbitrary: neither irreflexivity nor transitivity is required, and
either set or ambient type may be empty. -/
theorem chainHeight_sum_lex
    {α : Type u} {β : Type v} (rα : α → α → Prop) (rβ : β → β → Prop)
    (s : Set α) (t : Set β) :
    ((Sum.inl : α → α ⊕ β) '' s ∪ (Sum.inr : β → α ⊕ β) '' t).chainHeight
        (Sum.Lex rα rβ) = s.chainHeight rα + t.chainHeight rβ := by
  have hcard (a : Set α) (b : Set β) :
      ((Sum.inl : α → α ⊕ β) '' a ∪ (Sum.inr : β → α ⊕ β) '' b).encard =
        a.encard + b.encard := by
    rw [Set.encard_union_eq Set.disjoint_image_inl_image_inr,
      Sum.inl_injective.encard_image, Sum.inr_injective.encard_image]
  apply le_antisymm
  · rw [Set.chainHeight_eq_iSup]
    refine iSup_le fun c ↦ ?_
    have hleftsub : (Sum.inl : α → α ⊕ β) ⁻¹' c.1 ⊆ s := by
      simpa only [Set.preimage_union, Set.preimage_image_eq s Sum.inl_injective,
        Set.preimage_inl_image_inr, Set.union_empty] using
        (Set.preimage_mono (f := (Sum.inl : α → α ⊕ β)) c.2.1)
    have hrightsub : (Sum.inr : β → α ⊕ β) ⁻¹' c.1 ⊆ t := by
      simpa only [Set.preimage_union, Set.preimage_image_eq t Sum.inr_injective,
        Set.preimage_inr_image_inl, Set.empty_union] using
        (Set.preimage_mono (f := (Sum.inr : β → α ⊕ β)) c.2.1)
    calc
      c.1.encard =
          ((Sum.inl : α → α ⊕ β) '' (Sum.inl ⁻¹' c.1) ∪
            (Sum.inr : β → α ⊕ β) '' (Sum.inr ⁻¹' c.1)).encard :=
        congrArg Set.encard (Set.image_preimage_inl_union_image_preimage_inr c.1).symm
      _ = (Sum.inl ⁻¹' c.1).encard + (Sum.inr ⁻¹' c.1).encard := hcard _ _
      _ ≤ s.chainHeight rα + t.chainHeight rβ :=
        add_le_add
          (Set.encard_le_chainHeight_of_isChain s _ hleftsub
            (c.2.2.preimage_relEmbedding (RelEmbedding.sumLexInl rα rβ)))
          (Set.encard_le_chainHeight_of_isChain t _ hrightsub
            (c.2.2.preimage_relEmbedding (RelEmbedding.sumLexInr rα rβ)))
  · -- The empty chains inhabit the supremum indices even when the factors are empty.
    have : Nonempty {a : Set α // a ⊆ s ∧ IsChain rα a} :=
      ⟨⟨∅, Set.empty_subset s, IsChain.empty⟩⟩
    have : Nonempty {b : Set β // b ⊆ t ∧ IsChain rβ b} :=
      ⟨⟨∅, Set.empty_subset t, IsChain.empty⟩⟩
    rw [Set.chainHeight_eq_iSup s rα, Set.chainHeight_eq_iSup t rβ]
    refine ENat.iSup_add_iSup_le fun a b ↦ ?_
    rw [← hcard a.1 b.1]
    refine Set.encard_le_chainHeight_of_isChain _ _
      (Set.union_subset_union (Set.image_mono a.2.1) (Set.image_mono b.2.1)) ?_
    refine isChain_union.mpr
      ⟨a.2.2.image (RelEmbedding.sumLexInl rα rβ),
        b.2.2.image (RelEmbedding.sumLexInr rα rβ), ?_⟩
    rintro _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩ _
    exact Or.inl (Sum.Lex.sep x y)

/-- Chain heights add for the image of the tagged union in the lexicographic sum type synonym.
The less-than relation on the sum is the canonical `Sum.Lex.LT` induced by the given less-than
structures on the factors. No irreflexivity, transitivity or nonemptiness is required. -/
theorem chainHeight_toLex_sum
    {α : Type u} {β : Type v} [LT α] [LT β] (s : Set α) (t : Set β) :
    ((toLex : α ⊕ β → α ⊕ₗ β) ''
      ((Sum.inl : α → α ⊕ β) '' s ∪ (Sum.inr : β → α ⊕ β) '' t)).chainHeight
        (fun x y : α ⊕ₗ β => x < y) =
      s.chainHeight (fun x y : α => x < y) +
        t.chainHeight (fun x y : β => x < y) := by
  calc
    _ = ((Sum.inl : α → α ⊕ β) '' s ∪ (Sum.inr : β → α ⊕ β) '' t).chainHeight
        (Sum.Lex (fun x y : α => x < y) (fun x y : β => x < y)) :=
      chainHeight_eq_of_relIso _ (Sum.Lex.toLexRelIsoLT (α := α) (β := β))
    _ = _ := chainHeight_sum_lex _ _ s t

end Set
