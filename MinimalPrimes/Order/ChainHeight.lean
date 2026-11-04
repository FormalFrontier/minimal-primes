/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Height
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Chain heights of lexicographic products

`Set.chainHeight` is the supremum in `ENat` of the cardinalities of subsets whose distinct
points are pairwise comparable for a given relation. It counts vertices, not steps or ordinal
ranks. Pairwise comparability does not imply transitivity or a linear ordering by the relation.

For the relation `Prod.Lex rα rβ`, comparison uses `rα` in the first coordinate or equality of
first coordinates together with `rβ` in the second. The chain height of a product of sets is the
product of their chain heights when `rα` is irreflexive on the first set. No condition is required
on `rβ`, which may have loops. Loops of `rα` outside the first set are irrelevant.

Transport by `toLex` gives the corresponding formula for the canonical less-than relation on
`α ×ₗ β`. Only less-than structures and irreflexivity of the first relation are required; in
particular, the formula applies to arbitrary preorders without antisymmetry.

Empty factors have chain height zero, including `0 * ⊤ = 0 = ⊤ * 0` in `ENat`. A height of `⊤`
can arise from unbounded finite chain cardinalities without an infinite chain or a longest chain.

## Proof strategy

Products of comparable subsets give the lower bound by cardinal multiplication and ENat suprema.
For the upper bound, take a finite comparable subset, project to the first coordinate and count
its fibres. The first projection is a comparable subset, and local first irreflexivity makes
each fibre a comparable subset for the second relation. This argument never sorts a chain or
assumes either relation is transitive.

## References

The proof uses Mathlib's chain-height and finite-witness API in `Mathlib.Order.Height`
(Andrew Yang and Vlad Tsyrklevich), relation embeddings in `Mathlib.Order.RelIso.Basic`
(Mario Carneiro and contributors), finite-union cardinality bounds in
`Mathlib.Data.Set.Card.Arithmetic` (Pim Otte), and its set-cardinality, lexicographic product
and ENat supremum APIs.
-/

@[expose] public section

universe u v

namespace Set

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

end Set
