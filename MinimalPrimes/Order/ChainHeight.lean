/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sigma.Lex
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Directed
public import Mathlib.Order.Height
public import Mathlib.Order.PiLex
public import Mathlib.Order.ScottContinuity.Complete
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Prod
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Fin.Tuple

/-!
# Chain heights of unions, lexicographic products and dependent sums

`Set.chainHeight` is the supremum in `ENat` of the cardinalities of subsets whose distinct
points are pairwise comparable for a given relation. It counts vertices, not steps, dimensions
or ordinal ranks. Pairwise comparability does not imply transitivity or a linear ordering by the
relation.

The chain height of a union is at most the sum of the chain heights of its pieces, with no
relation laws required. The pieces may overlap or be empty, and infinite heights are allowed.
For disjoint pieces whose cross pairs compare in either direction, the bound is an equality.

For the relation `Prod.Lex rα rβ`, comparison uses `rα` in the first coordinate or equality of
first coordinates together with `rβ` in the second. The chain height of a product of sets is the
product of their chain heights when `rα` is irreflexive on the first set. No condition is required
on `rβ`, which may have loops. Loops of `rα` outside the first set are irrelevant.

For a finite linearly ordered index and dependent supports `s i`, the height of
`Set.pi Set.univ s` under `Pi.Lex (<) q` is the product of the fibre heights, provided that
coordinates preceding a nonsubsingleton support have no loops along supported functions.
This condition is vacuous for an empty product support. The last varying support and trailing
singleton supports may have loops, but an earlier singleton support still needs the condition
when a later support varies. Prefix comparison uses equality, not preorder equivalence.
The index and fibre universes are independent, and the fibres need no order laws or finiteness.

For `Sum.Lex rα rβ`, comparison within each tag uses the corresponding factor relation, and
every left-tagged point precedes every right-tagged point. The chain height of the union of the
two tagged images is the sum of the factor chain heights, with no relation laws required. In
particular, loops and directed cycles are allowed in either factor. Unlike the product formula,
the sum formula needs no first-irreflexivity hypothesis.

Transport by `toLex` gives the corresponding formulas for the canonical less-than relations on
`α ×ₗ β` and `α ⊕ₗ β`. The sum formula requires only the given less-than structures; the product
formula additionally requires first irreflexivity. Neither formula requires antisymmetry or
transitivity. The two factor types may lie in independent universes.

For `Sigma.Lex r R`, an arbitrary subset has height equal to the supremum of finite sums of
its fiber heights when its active indices are pairwise comparable for `r` and `r` is
irreflexive on those indices. Index and fiber universes are independent. No transitivity,
global index order, finiteness, countability or nonemptiness assumption is needed. Inactive
indices, including those carrying loops, are irrelevant. An active index loop can compare
distinct fiber points even when their fiber relation is false, so active irreflexivity matters.
The formula is
`S.chainHeight (Sigma.Lex r R) = ⨆ J : Finset ι, ∑ i ∈ J,
((Sigma.mk i) ⁻¹' S).chainHeight (R i)`.

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

## Directed suprema of relations

For a fixed subset, chain height is Scott continuous as a function of the relation, ordered by
pointwise implication. Scott continuity tests nonempty directed sets of relations, not arbitrary
joins or the empty supremum. No order or relation laws on the carrier are required.

For an indexed directed family of relations, including an empty family, the height of the
pointwise supremum is the join of the height of the false relation and the supremum of the
members' heights. The false-relation baseline is zero on the empty subset and one on any
nonempty subset. In particular, a singleton subset and an empty index have height one on the
left, whereas the empty supremum of heights is zero. Nondirected joins can increase height:
on three points, the relations with edges `0 → 1, 0 → 2` and `1 → 2` each have height two,
but their join has height three. Loops and directed cycles are allowed.

## Disjoint sums

For `Sum.LiftRel rα rβ`, no left-tagged point compares with a right-tagged point in either
direction. The chain height of the tagged union is therefore the maximum of the factor
heights. `Set.chainHeight_sum` specializes this to the ordinary sum less-than relation induced
by exactly the two given less-than structures. No relation laws are required.

More generally, `Set.chainHeight_iUnion_of_not_rel` gives the supremum formula for an
arbitrary family of sets on one carrier when points in opposite exclusive pieces cannot
compare. Its index may be any sort, including an empty one, and the original family need not
be inclusion-directed. For each pair, the no-cross condition concerns only its opposite
exclusive pieces; all loops remain unrestricted. The binary `Set.chainHeight_union_of_not_rel`
is its two-piece maximum specialization.

## Proof strategy

Products of comparable subsets give the lower bound by cardinal multiplication and ENat suprema.
For the upper bound, take a finite comparable subset, project to the first coordinate and count
its fibres. The first projection is a comparable subset, and local first irreflexivity makes
each fibre a comparable subset for the second relation. This argument never sorts a chain or
assumes either relation is transitive.

For finite dependent products, the stock `Fin.consEquiv` and `Fin.pi_lex_lt_cons_cons` identify
the relation and supports with a binary lexicographic product. Induction then reuses the binary
height theorem with its subsingleton-tail case. The empty support is handled before choosing a
supported function. An order-preserving `Fintype.orderIsoFinOfCardEq` and `Equiv.piCongrLeft`
transport this formula to any finite linear index, including the empty index, whose product
has height one. The canonical `toLex` image formula requires only less-than structures on the
fibres.

For unions, intersect a comparable subset with the two pieces. Each restriction remains
comparable, and their union is the original subset. Cardinality subadditivity and the two
piece-height bounds give the upper bound without any relation laws.

For disjoint cross-comparable unions, two subset chains have a chain union whose cardinality
is the sum of their cardinalities. Taking the two suprema gives equality in the union bound;
empty chains supply the nonempty internal witness types even for empty pieces. The binary
lexicographic sum then uses this union formula and stock relation-embedding transport.

For dependent lexicographic sums, the tagged fibers are disjoint and cover the given subset.
On an active fiber, index irreflexivity makes `Sigma.mk` a relation embedding; inactive fibers
are empty. Finite induction applies the same union formula to finite partial unions. These
partial unions are inclusion-directed, so the existing directed-union formula supplies the
supremum of finite sums, without choosing points, a longest chain or an infinite chain.

For directed unions, every finite positive chain-cardinality witness fits in one piece.
A point of the witness supplies the local nonempty range needed by the finite-containment
theorem; the zero bound requires no index. Testing all natural lower bounds also handles top.

For directed relation suprema, a finite chain witness requires simultaneous capture of all
comparisons between distinct points, not just the points or successive edges. Finite
containment in one directed relation preserves the same comparable subset. Natural-number
bounds handle unbounded finite heights without choosing an infinite or longest chain. The
false-relation baseline accounts for empty indexed families and chains of size at most one.

For exclusive-piece unions, the intersections of any comparable subset with the pieces are
inclusion-comparable: witnesses to failure of both inclusions would contradict the no-cross
hypothesis. These traces form a directed family with the same union as the comparable subset,
so the directed-union formula and subset monotonicity bound its cardinality. No single piece
need contain the entire chain; nested finite initial segments of an infinite chain illustrate
why this is essential. Taking the defining supremum gives the upper bound, while inclusion of
each piece gives the lower bound. The binary maximum formula is the Bool-indexed specialization.
The disjoint-sum formulas then use the stock factor relation embeddings and whole image-height
transport to identify the tagged-piece heights. No longest or infinite chain is chosen.

## References

The proof uses Mathlib's chain-height and finite-witness API in `Mathlib.Order.Height`
(Andrew Yang and Vlad Tsyrklevich), relation embeddings in `Mathlib.Order.RelIso.Basic`
(Mario Carneiro and contributors), finite-union cardinality bounds in
`Mathlib.Data.Set.Card.Arithmetic` (Pim Otte), and its set-cardinality, lexicographic product
and ENat supremum APIs. The union bound uses `Set.encard_union_le` from `Mathlib.Data.Set.Card`
(Peter Nelson). The sum formula uses the sum relation API in Lean's `Init.Data.Sum.Basic`
(Mario Carneiro and Yury G. Kudryashov), the canonical lexicographic sum and relation isomorphism
in `Mathlib.Data.Sum.Order` (Yaël Dillies), and Mathlib's disjoint-cardinality addition API.
The directed-family predicate is from `Mathlib.Order.Directed`
(Johannes Hölzl and Yaël Dillies). Finite containment in directed unions uses
`Mathlib.Data.Set.Finite.Lattice` (Johannes Hölzl, Mario Carneiro and Kyle Miller).
The Scott-continuity predicate and complete-lattice characterization are from
`Mathlib.Order.ScottContinuity` and `Mathlib.Order.ScottContinuity.Complete`
(Christopher Hoskin). Restriction and relation monotonicity of comparable subsets use
`IsChain.mono` and `IsChain.mono_rel` from `Mathlib.Order.Preorder.Chain` (Johannes Hölzl).
Finiteness of comparison pairs uses `Mathlib.Basic.Finite.Prod` (Kyle Miller).
The exclusive-piece union proof generalizes the earlier Formal Frontier binary no-cross
formalization, composing its directed-union theorem with Mathlib's chain-cardinality,
intersection and indexed-supremum APIs. The binary specialization uses the Bool supremum API.
The sum formulas reuse `RelEmbedding.sumLexInl/Inr`, `RelEmbedding.sumLiftRelInl/Inr` and the
whole `Set.chainHeight_eq_of_relEmbedding` transport from those Mathlib APIs. The disjoint-sum
formula also uses the cross-tag negation lemmas from Lean's Sum relation API and `Sum.lt_def`
for the ordinary-sum specialization.
The dependent-product proof uses `Mathlib.Order.PiLex` (Chris Hughes),
`Mathlib.Order.Fin.Tuple` (Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel and Chris Hughes),
`Fin.consEquiv` from `Mathlib.Data.Fin.Tuple.Basic` (the same authors and Antoine Chambert-Loir),
and the ordered finite reindexing API from `Mathlib.Data.Finset.Sort` (Mario Carneiro).
Dependent function and support transport use `Equiv.piCongrLeft` from
`Mathlib.Logic.Equiv.Basic` (Mario Carneiro and contributors). The Pi-support preimage API is from
`Mathlib.Data.Set.Prod` (Mario Carneiro, Johannes Hölzl and Patrick Massot).
Finite-product induction uses `Mathlib.Algebra.BigOperators.Fin`
(Yury Kudryashov and Anne Baanen).

The dependent-sum relation is Mathlib's `Sigma.Lex`
from `Mathlib.Data.Sigma.Lex` (Yaël Dillies); the disjoint cross-comparable union statement
generalizes the earlier Formal Frontier binary lexicographic-sum core. Finite partial unions
use `Finset.set_biUnion_insert` and `Set.iUnion_eq_iUnion_finset` from
`Mathlib.Order.CompleteLattice.Finset` (Mario Carneiro and contributors), together with
`Finset.isDirected_le` from `Mathlib.Data.Finset.Basic`
(Leonardo de Moura, Jeremy Avigad, Minchao Wu and Mario Carneiro).
-/

@[expose] public section

universe u v w

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

/-- Relations that agree on distinct points of a set have the same chain height on that set.
The relations may differ on the diagonal and outside the set. -/
theorem chainHeight_congr_rel
    {α : Type u} (s : Set α) {r r' : α → α → Prop}
    (h : s.Pairwise (fun a b ↦ r a b ↔ r' a b)) :
    s.chainHeight r = s.chainHeight r' := by
  have hc (t : Set α) (hts : t ⊆ s) : IsChain r t ↔ IsChain r' t := by
    constructor
    · intro ht
      refine Set.Pairwise.imp_on ht ?_
      intro a ha b hb hab
      exact Or.imp (h (hts ha) (hts hb) hab).mp
        (h (hts hb) (hts ha) hab.symm).mp
    · intro ht
      refine Set.Pairwise.imp_on ht ?_
      intro a ha b hb hab
      exact Or.imp (h (hts ha) (hts hb) hab).mpr
        (h (hts hb) (hts ha) hab.symm).mpr
  apply le_antisymm
  · rw [Set.chainHeight_eq_iSup s r]
    exact iSup_le fun t ↦ Set.encard_le_chainHeight_of_isChain s t.1 t.2.1
      ((hc t.1 t.2.1).mp t.2.2)
  · rw [Set.chainHeight_eq_iSup s r']
    exact iSup_le fun t ↦ Set.encard_le_chainHeight_of_isChain s t.1 t.2.1
      ((hc t.1 t.2.1).mpr t.2.2)

/-- Chain heights multiply for a lexicographic product when every first-coordinate loop
in the first support forces the second support to be subsingleton. -/
theorem chainHeight_prod_lex_of_refl_imp_subsingleton
    {α : Type u} {β : Type v} (rα : α → α → Prop) (rβ : β → β → Prop)
    (s : Set α) (t : Set β) (hs : ∀ a ∈ s, rα a a → t.Subsingleton) :
    (s ×ˢ t).chainHeight (Prod.Lex rα rβ) = s.chainHeight rα * t.chainHeight rβ := by
  let rα' : α → α → Prop := fun a b ↦ rα a b ∧ a ≠ b
  have hα : s.chainHeight rα' = s.chainHeight rα := by
    apply chainHeight_congr_rel s
    intro a _ b _ hab
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hab⟩⟩
  calc
    (s ×ˢ t).chainHeight (Prod.Lex rα rβ) =
        (s ×ˢ t).chainHeight (Prod.Lex rα' rβ) := by
      apply chainHeight_congr_rel (s ×ˢ t)
      intro x hx y hy hxy
      constructor
      · intro h
        rcases Prod.lex_iff.mp h with h | ⟨ha, hb⟩
        · refine Prod.lex_iff.mpr (Or.inl ⟨h, ?_⟩)
          intro ha
          have hloop : rα x.1 x.1 := by simpa only [← ha] using h
          exact hxy (Prod.ext ha (hs x.1 hx.1 hloop hx.2 hy.2))
        · exact Prod.lex_iff.mpr (Or.inr ⟨ha, hb⟩)
      · intro h
        rcases Prod.lex_iff.mp h with h | ⟨ha, hb⟩
        · exact Prod.lex_iff.mpr (Or.inl h.1)
        · exact Prod.lex_iff.mpr (Or.inr ⟨ha, hb⟩)
    _ = s.chainHeight rα' * t.chainHeight rβ :=
      chainHeight_prod_lex rα' rβ s t (fun a _ h ↦ h.2 rfl)
    _ = s.chainHeight rα * t.chainHeight rβ := by rw [hα]

section PiLex

private theorem fin_cons_mem_univ_pi
    {n : ℕ} {β : Fin (n + 1) → Type v} (s : ∀ i, Set (β i))
    (a : β 0) (f : ∀ i : Fin n, β i.succ) :
    Fin.cons a f ∈ Set.pi Set.univ s ↔
      a ∈ s 0 ∧ f ∈ Set.pi Set.univ (fun i : Fin n => s i.succ) := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem chainHeight_pi_lex_fin_cons
    {n : ℕ} {β : Fin (n + 1) → Type v}
    (q : ∀ {i}, β i → β i → Prop) (s : ∀ i, Set (β i)) :
    (Set.pi Set.univ s).chainHeight (Pi.Lex (fun i j => i < j) (@q)) =
      (s 0 ×ˢ Set.pi Set.univ (fun i : Fin n => s i.succ)).chainHeight
        (Prod.Lex (@q 0)
          (Pi.Lex (fun i j : Fin n => i < j) (@fun i : Fin n => @q i.succ))) := by
  let e : Prod.Lex (@q 0)
        (Pi.Lex (fun i j : Fin n => i < j) (@fun i : Fin n => @q i.succ)) ≃r
      Pi.Lex (fun i j : Fin (n + 1) => i < j) (@q) :=
    { toEquiv := Fin.consEquiv β
      map_rel_iff' := by
        intro x y
        exact (Fin.pi_lex_lt_cons_cons q).trans Prod.lex_iff.symm }
  have hsupport : e '' (s 0 ×ˢ Set.pi Set.univ (fun i : Fin n => s i.succ)) =
      Set.pi Set.univ s := by
    change (Fin.consEquiv β) '' _ = _
    rw [Equiv.image_eq_preimage_symm]
    ext f
    change (f 0 ∈ s 0 ∧ Fin.tail f ∈
      Set.pi Set.univ (fun i : Fin n => s i.succ)) ↔ f ∈ Set.pi Set.univ s
    rw [← fin_cons_mem_univ_pi s, Fin.cons_self_tail]
  rw [← hsupport]
  exact chainHeight_eq_of_relIso _ e

private theorem chainHeight_fin_pi_lex (n : ℕ) :
    ∀ (β : Fin n → Type v) (q : ∀ {i}, β i → β i → Prop) (s : ∀ i, Set (β i)),
      (∀ f ∈ Set.pi Set.univ s, ∀ i j : Fin n,
        i < j → ¬ (s j).Subsingleton → ¬ q (f i) (f i)) →
      (Set.pi Set.univ s).chainHeight (Pi.Lex (fun i j => i < j) (@q)) =
        ∏ i, (s i).chainHeight (@q i) := by
  induction n with
  | zero =>
      intro β q s _
      have hsupport : Set.pi Set.univ s = {fun i : Fin 0 => Fin.elim0 i} :=
        Set.subsingleton_of_subsingleton.eq_singleton_of_mem (fun i _ => Fin.elim0 i)
      rw [hsupport, ← Set.encard_eq_chainHeight_of_isChain _ IsChain.singleton]
      simp only [Set.encard_singleton, Fin.prod_univ_zero]
  | succ n ih =>
      intro β q s hs
      classical
      by_cases hsupport : (Set.pi Set.univ s).Nonempty
      · obtain ⟨f, hf⟩ := hsupport
        have htail : ∀ g ∈ Set.pi Set.univ (fun i : Fin n => s i.succ),
            ∀ i j : Fin n, i < j → ¬ (s j.succ).Subsingleton → ¬ q (g i) (g i) := by
          intro g hg i j hij hj
          have hcons : Fin.cons (f 0) g ∈ Set.pi Set.univ s :=
            (fin_cons_mem_univ_pi s _ _).mpr ⟨hf 0 (Set.mem_univ _), hg⟩
          simpa only [Fin.cons_succ] using
            hs (Fin.cons (f 0) g) hcons i.succ j.succ (Fin.strictMono_succ hij) hj
        have hhead : ∀ a ∈ s 0, q a a →
            (Set.pi Set.univ (fun i : Fin n => s i.succ)).Subsingleton := by
          intro a ha hqa
          apply Set.subsingleton_univ_pi
          intro j
          by_contra hj
          have hcons : Fin.cons a (Fin.tail f) ∈ Set.pi Set.univ s :=
            (fin_cons_mem_univ_pi s _ _).mpr
              ⟨ha, fun i _ => hf i.succ (Set.mem_univ _)⟩
          exact hs (Fin.cons a (Fin.tail f)) hcons 0 j.succ (Fin.succ_pos j) hj
            (by simpa only [Fin.cons_zero] using hqa)
        calc
          _ = (s 0 ×ˢ Set.pi Set.univ (fun i : Fin n => s i.succ)).chainHeight
              (Prod.Lex (@q 0)
                (Pi.Lex (fun i j : Fin n => i < j) (@fun i : Fin n => @q i.succ))) :=
            chainHeight_pi_lex_fin_cons q s
          _ = (s 0).chainHeight (@q 0) *
              (Set.pi Set.univ (fun i : Fin n => s i.succ)).chainHeight
                (Pi.Lex (fun i j : Fin n => i < j) (@fun i : Fin n => @q i.succ)) :=
            chainHeight_prod_lex_of_refl_imp_subsingleton _ _ _ _ hhead
          _ = (s 0).chainHeight (@q 0) * ∏ i : Fin n, (s i.succ).chainHeight (@q i.succ) := by
            rw [ih (fun i => β i.succ) (@fun i : Fin n => @q i.succ)
              (fun i => s i.succ) htail]
          _ = _ :=
            (Fin.prod_univ_succ (fun i : Fin (n + 1) => (s i).chainHeight (@q i))).symm
      · have hempty : Set.pi Set.univ s = ∅ := Set.not_nonempty_iff_eq_empty.mp hsupport
        obtain ⟨i, hi⟩ := Set.univ_pi_eq_empty_iff.mp hempty
        rw [hempty, Set.chainHeight_empty]
        exact (Finset.prod_eq_zero (Finset.mem_univ i)
          ((Set.chainHeight_eq_zero_iff (s i) (@q i)).mpr hi)).symm

private theorem chainHeight_pi_lex_reindex
    {ι : Type u} {κ : Type w} {β : ι → Type v}
    {rι : ι → ι → Prop} {rκ : κ → κ → Prop}
    (e : rκ ≃r rι) (q : ∀ {i}, β i → β i → Prop) (s : ∀ i, Set (β i)) :
    (Set.pi Set.univ (fun i : κ => s (e i))).chainHeight
        (Pi.Lex rκ (@fun i : κ => @q (e i))) =
      (Set.pi Set.univ s).chainHeight (Pi.Lex rι (@q)) := by
  let E : Pi.Lex rι (@q) ≃r Pi.Lex rκ (@fun i : κ => @q (e i)) :=
    { toEquiv := (Equiv.piCongrLeft β e.toEquiv).symm
      map_rel_iff' := by
        intro f g
        change (∃ i : κ, (∀ j, rκ j i → f (e j) = g (e j)) ∧
          q (f (e i)) (g (e i))) ↔ Pi.Lex rι (@q) f g
        constructor
        · rintro ⟨i, hpre, hq⟩
          refine ⟨e i, ?_, hq⟩
          intro j hji
          obtain ⟨k, rfl⟩ := e.surjective j
          exact hpre k (e.map_rel_iff.mp hji)
        · rintro ⟨i, hpre, hq⟩
          obtain ⟨k, rfl⟩ := e.surjective i
          exact ⟨k, fun j hji => hpre (e j) (e.map_rel_iff.mpr hji), hq⟩ }
  have hsupport : E '' Set.pi Set.univ s = Set.pi Set.univ (fun i : κ => s (e i)) := by
    change (Equiv.piCongrLeft β e.toEquiv).symm '' _ = _
    rw [Equiv.image_symm_eq_preimage]
    exact Equiv.piCongrLeft_preimage_univ_pi e.toEquiv s
  rw [← hsupport]
  exact chainHeight_eq_of_relIso _ E

/-- Chain heights multiply for a finite dependent lexicographic product if coordinates
preceding a nonsubsingleton support have no loops along supported functions. -/
theorem chainHeight_pi_lex
    {ι : Type u} {β : ι → Type v} [Fintype ι] [LinearOrder ι]
    (q : ∀ {i}, β i → β i → Prop) (s : ∀ i, Set (β i))
    (hs : ∀ f ∈ Set.pi Set.univ s, ∀ i j : ι,
      i < j → ¬ (s j).Subsingleton → ¬ q (f i) (f i)) :
    (Set.pi Set.univ s).chainHeight (Pi.Lex (fun i j : ι => i < j) (@q)) =
      ∏ i, (s i).chainHeight (@q i) := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have hs' : ∀ f ∈ Set.pi Set.univ (fun i : Fin (Fintype.card ι) => s (e i)),
      ∀ i j : Fin (Fintype.card ι), i < j → ¬ (s (e j)).Subsingleton →
        ¬ q (f i) (f i) := by
    intro f hf i j hij hj
    have hf' : Equiv.piCongrLeft β e.toEquiv f ∈ Set.pi Set.univ s := by
      change f ∈ Equiv.piCongrLeft β e.toEquiv ⁻¹' Set.pi Set.univ s
      rw [Equiv.piCongrLeft_preimage_univ_pi]
      exact hf
    have hfi : Equiv.piCongrLeft β e.toEquiv f (e i) = f i :=
      Equiv.piCongrLeft_apply_apply β e.toEquiv f i
    simpa only [hfi] using
      hs (Equiv.piCongrLeft β e.toEquiv f) hf' (e i) (e j) (e.lt_iff_lt.mpr hij) hj
  calc
    _ = (Set.pi Set.univ (fun i : Fin (Fintype.card ι) => s (e i))).chainHeight
        (Pi.Lex (fun i j : Fin (Fintype.card ι) => i < j)
          (@fun i : Fin (Fintype.card ι) => @q (e i))) :=
      (chainHeight_pi_lex_reindex e.toRelIsoLT q s).symm
    _ = ∏ i : Fin (Fintype.card ι), (s (e i)).chainHeight (@q (e i)) :=
      chainHeight_fin_pi_lex _ _ _ _ hs'
    _ = _ := e.toEquiv.prod_comp (fun i => (s i).chainHeight (@q i))

/-- Chain heights multiply for the `toLex` image of a finite dependent product, with the
canonical less-than relation, if coordinates preceding a nonsubsingleton support have no loops
along supported functions. Only less-than structures are required on the fibres. -/
theorem chainHeight_toLex_pi
    {ι : Type u} {β : ι → Type v} [Fintype ι] [LinearOrder ι]
    [∀ i, LT (β i)] (s : ∀ i, Set (β i))
    (hs : ∀ f ∈ Set.pi Set.univ s, ∀ i j : ι,
      i < j → ¬ (s j).Subsingleton → ¬ (f i < f i)) :
    ((toLex : (∀ i, β i) → Lex (∀ i, β i)) '' Set.pi Set.univ s).chainHeight
        (fun x y : Lex (∀ i, β i) => x < y) =
      ∏ i, (s i).chainHeight (fun x y : β i => x < y) := by
  calc
    _ = (Set.pi Set.univ s).chainHeight
        (Pi.Lex (fun i j : ι => i < j) (fun {i} (x y : β i) => x < y)) :=
      chainHeight_eq_of_relIso _
        (RelIso.ofOnFun (fun x y : Lex (∀ i, β i) => x < y) toLex)
    _ = _ := chainHeight_pi_lex (fun {i} (x y : β i) => x < y) s hs

end PiLex

/-- The chain height of a union is at most the sum of the chain heights of its pieces.
The relation is arbitrary, the pieces may overlap, and either piece or the ambient type
may be empty. -/
theorem chainHeight_union_le
    {α : Type u} (r : α → α → Prop) (s t : Set α) :
    (s ∪ t).chainHeight r ≤ s.chainHeight r + t.chainHeight r := by
  rw [Set.chainHeight_eq_iSup]
  refine iSup_le fun c ↦ ?_
  calc
    c.1.encard = (c.1 ∩ s ∪ c.1 ∩ t).encard := by
      rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr c.2.1]
    _ ≤ (c.1 ∩ s).encard + (c.1 ∩ t).encard := Set.encard_union_le _ _
    _ ≤ s.chainHeight r + t.chainHeight r :=
      add_le_add
        (Set.encard_le_chainHeight_of_isChain s _ Set.inter_subset_right
          (c.2.2.mono Set.inter_subset_left))
        (Set.encard_le_chainHeight_of_isChain t _ Set.inter_subset_right
          (c.2.2.mono Set.inter_subset_left))

/-- Chain heights add for disjoint sets whose cross pairs are comparable in either direction.
The relation is arbitrary; no transitivity, irreflexivity or nonemptiness is required. -/
theorem chainHeight_union_of_disjoint_of_cross
    {X : Type w} (q : X → X → Prop) (s t : Set X)
    (hd : Disjoint s t) (hcross : ∀ a ∈ s, ∀ b ∈ t, q a b ∨ q b a) :
    (s ∪ t).chainHeight q = s.chainHeight q + t.chainHeight q := by
  apply le_antisymm (chainHeight_union_le q s t)
  -- Empty chains inhabit the witness types, including when either piece is empty.
  have : Nonempty {a : Set X // a ⊆ s ∧ IsChain q a} :=
    ⟨⟨∅, Set.empty_subset s, IsChain.empty⟩⟩
  have : Nonempty {b : Set X // b ⊆ t ∧ IsChain q b} :=
    ⟨⟨∅, Set.empty_subset t, IsChain.empty⟩⟩
  rw [Set.chainHeight_eq_iSup s q, Set.chainHeight_eq_iSup t q]
  refine ENat.iSup_add_iSup_le fun a b ↦ ?_
  rw [← Set.encard_union_eq (hd.mono a.2.1 b.2.1)]
  refine Set.encard_le_chainHeight_of_isChain _ _
    (Set.union_subset_union a.2.1 b.2.1) ?_
  exact isChain_union.mpr ⟨a.2.2, b.2.2,
    fun x hx y hy _ ↦ hcross x (a.2.1 hx) y (b.2.1 hy)⟩

/-- Chain heights add for the union of the two tagged images under the lexicographic sum
relation. The relations are arbitrary: neither irreflexivity nor transitivity is required, and
either set or ambient type may be empty. -/
theorem chainHeight_sum_lex
    {α : Type u} {β : Type v} (rα : α → α → Prop) (rβ : β → β → Prop)
    (s : Set α) (t : Set β) :
    ((Sum.inl : α → α ⊕ β) '' s ∪ (Sum.inr : β → α ⊕ β) '' t).chainHeight
        (Sum.Lex rα rβ) = s.chainHeight rα + t.chainHeight rβ := by
  calc
    _ = ((Sum.inl : α → α ⊕ β) '' s).chainHeight (Sum.Lex rα rβ) +
        ((Sum.inr : β → α ⊕ β) '' t).chainHeight (Sum.Lex rα rβ) := by
      apply chainHeight_union_of_disjoint_of_cross _ _ _
        Set.disjoint_image_inl_image_inr
      rintro _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩
      exact Or.inl (Sum.Lex.sep x y)
    _ = _ := congrArg₂ (· + ·)
      (Set.chainHeight_eq_of_relEmbedding s (RelEmbedding.sumLexInl rα rβ))
      (Set.chainHeight_eq_of_relEmbedding t (RelEmbedding.sumLexInr rα rβ))

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

/-- Chain heights add over a finite family of pairwise disjoint sets whose cross pairs are
comparable in either direction. Disjointness and cross comparability are required only for
indices in `J`. The relation is arbitrary; empty pieces and infinite heights are allowed. -/
theorem chainHeight_biUnion_finset_of_disjoint_of_cross
    {X : Type w} {κ : Type u} (q : X → X → Prop) (P : κ → Set X) (J : Finset κ)
    (hd : (↑J : Set κ).Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcross : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, q a b ∨ q b a) :
    (⋃ i ∈ J, P i).chainHeight q = ∑ i ∈ J, (P i).chainHeight q := by
  classical
  revert hd hcross
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    intro hd hcross
    have hJ := ih
      (fun j hj k hk hjk ↦
        hd (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj k hk hjk ↦
        hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    have hdisj : Disjoint (P i) (⋃ j ∈ J, P j) := by
      refine Set.disjoint_left.mpr ?_
      intro x hxi hxJ
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxJ
      obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxj
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hi hj
      exact Set.disjoint_left.mp
        (hd (Finset.mem_insert_self i J) (Finset.mem_insert_of_mem hj) hij) hxi hxj
    have hcomp : ∀ a ∈ P i, ∀ b ∈ ⋃ j ∈ J, P j, q a b ∨ q b a := by
      intro a ha b hb
      obtain ⟨j, hbj⟩ := Set.mem_iUnion.mp hb
      obtain ⟨hj, hbj⟩ := Set.mem_iUnion.mp hbj
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hi hj
      exact hcross i (Finset.mem_insert_self i J) j (Finset.mem_insert_of_mem hj) hij a ha b hbj
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi,
      chainHeight_union_of_disjoint_of_cross q _ _ hdisj hcomp, hJ]

private theorem chainHeight_image_sigma_mk
    {ι : Type u} {α : ι → Type v}
    (r : ι → ι → Prop) (R : ∀ i, α i → α i → Prop)
    (S : Set (Σ i, α i))
    (hirr : ∀ i ∈ Sigma.fst '' S, ¬ r i i) (i : ι) :
    (Sigma.mk i '' ((Sigma.mk i) ⁻¹' S)).chainHeight (Sigma.Lex r R) =
      ((Sigma.mk i) ⁻¹' S).chainHeight (R i) := by
  classical
  by_cases hi : i ∈ Sigma.fst '' S
  · let e : R i ↪r Sigma.Lex r R :=
      { toFun := Sigma.mk i
        inj' := sigma_mk_injective
        map_rel_iff' := by
          intro a b
          constructor
          · intro hab
            rcases Sigma.lex_iff.mp hab with hii | ⟨h, hR⟩
            · exact (hirr i hi hii).elim
            · exact hR
          · intro hab
            exact Sigma.Lex.right a b hab }
    exact chainHeight_eq_of_relEmbedding ((Sigma.mk i) ⁻¹' S) e
  · have hF : (Sigma.mk i) ⁻¹' S = ∅ := by
      ext a
      constructor
      · intro ha
        exact (hi ⟨⟨i, a⟩, ha, rfl⟩).elim
      · intro ha
        exact ha.elim
    simp only [hF, Set.image_empty, Set.chainHeight_empty]

private theorem sigma_eq_iUnion_image_preimage
    {ι : Type u} {α : ι → Type v} (S : Set (Σ i, α i)) :
    S = ⋃ i, Sigma.mk i '' ((Sigma.mk i) ⁻¹' S) := by
  ext x
  rcases x with ⟨i, a⟩
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨i, ⟨a, hx, rfl⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨j, b, hb, hba⟩
    exact hba ▸ hb

private theorem disjoint_image_sigma_mk
    {ι : Type u} {α : ι → Type v} (S : Set (Σ i, α i))
    (i j : ι) (hij : i ≠ j) :
    Disjoint (Sigma.mk i '' ((Sigma.mk i) ⁻¹' S))
      (Sigma.mk j '' ((Sigma.mk j) ⁻¹' S)) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  rcases hx with ⟨a, _, hax⟩
  rcases hy with ⟨b, _, hbx⟩
  exact hij (congrArg Sigma.fst (hax.trans hbx.symm))

private theorem sigma_lex_cross_images
    {ι : Type u} {α : ι → Type v}
    (r : ι → ι → Prop) (R : ∀ i, α i → α i → Prop)
    (S : Set (Σ i, α i))
    (hchain : IsChain r (Sigma.fst '' S)) (i j : ι) (hij : i ≠ j) :
    ∀ x ∈ Sigma.mk i '' ((Sigma.mk i) ⁻¹' S),
      ∀ y ∈ Sigma.mk j '' ((Sigma.mk j) ⁻¹' S),
        Sigma.Lex r R x y ∨ Sigma.Lex r R y x := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  have hi : i ∈ Sigma.fst '' S := ⟨⟨i, a⟩, ha, rfl⟩
  have hj : j ∈ Sigma.fst '' S := ⟨⟨j, b⟩, hb, rfl⟩
  rcases hchain hi hj hij with h | h
  · exact Or.inl (Sigma.Lex.left a b h)
  · exact Or.inr (Sigma.Lex.left b a h)


/-- The chain height of a subset of a dependent lexicographic sum is the supremum of the
finite sums of its fiber heights. Only the active indices must be pairwise comparable and
irreflexive for the index relation. The fiber relations are arbitrary, the index and fiber
universes are independent, and empty fibers contribute zero. A height of top need not be
attained by any chain. -/
theorem chainHeight_sigma_lex
    {ι : Type u} {α : ι → Type v}
    (r : ι → ι → Prop) (R : ∀ i, α i → α i → Prop) (S : Set (Σ i, α i))
    (hchain : IsChain r (Sigma.fst '' S))
    (hirr : ∀ i ∈ Sigma.fst '' S, ¬ r i i) :
    S.chainHeight (Sigma.Lex r R) =
      ⨆ J : Finset ι, ∑ i ∈ J, ((Sigma.mk i) ⁻¹' S).chainHeight (R i) := by
  classical
  let P (i : ι) : Set (Σ i, α i) := Sigma.mk i '' ((Sigma.mk i) ⁻¹' S)
  have hfinite (J : Finset ι) :
      (⋃ i ∈ J, P i).chainHeight (Sigma.Lex r R) =
        ∑ i ∈ J, ((Sigma.mk i) ⁻¹' S).chainHeight (R i) := by
    rw [chainHeight_biUnion_finset_of_disjoint_of_cross (Sigma.Lex r R) P J
      (fun i _ j _ hij ↦ disjoint_image_sigma_mk S i j hij)
      (fun i _ j _ hij ↦ sigma_lex_cross_images r R S hchain i j hij)]
    exact Finset.sum_congr rfl fun i _ ↦ chainHeight_image_sigma_mk r R S hirr i
  have hmono : Monotone (fun J : Finset ι ↦ ⋃ i ∈ J, P i) := by
    intro J K hJK x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hJK hi, hxi⟩⟩
  calc
    _ = (⋃ i, P i).chainHeight (Sigma.Lex r R) :=
      congrArg (fun t ↦ t.chainHeight (Sigma.Lex r R)) (sigma_eq_iUnion_image_preimage S)
    _ = (⋃ J : Finset ι, ⋃ i ∈ J, P i).chainHeight (Sigma.Lex r R) := by
      rw [Set.iUnion_eq_iUnion_finset P]
    _ = ⨆ J : Finset ι, (⋃ i ∈ J, P i).chainHeight (Sigma.Lex r R) :=
      chainHeight_iUnion_of_directed _ _ hmono.directed_le
    _ = _ := iSup_congr hfinite

/-- On a fixed subset, chain height is Scott continuous in the relation ordered by pointwise
implication. Scott continuity preserves suprema of nonempty directed sets of relations; it
requires neither bottom preservation nor preservation of nondirected joins. -/
theorem scottContinuous_chainHeight
    {α : Type u} (s : Set α) :
    ScottContinuous (fun r : α → α → Prop => s.chainHeight r) := by
  have hmono : Monotone (Set.chainHeight s) := by
    intro r r' hrr'
    rw [Set.chainHeight_eq_iSup s r]
    refine iSup_le fun t ↦ ?_
    exact Set.encard_le_chainHeight_of_isChain s t.1 t.2.1
      (t.2.2.mono_rel fun a b hab ↦ hrr' a b hab)
  apply ScottContinuous.of_map_sSup
  intro d hdne hd
  apply le_antisymm
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
    obtain ⟨t, hts, hcard, htchain⟩ := Set.exists_isChain_of_le_chainHeight n hn
    have htfin : t.Finite := Set.finite_of_encard_eq_coe hcard
    -- Capture all off-diagonal comparisons in one relation, without sorting the chain.
    let C (q : α → α → Prop) : Set (α × α) :=
      {p | q p.1 p.2 ∨ q p.2 p.1}
    let p : Set (α × α) := {p | p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2}
    have hpfin : p.Finite :=
      (htfin.prod htfin).subset fun _ hp ↦ ⟨hp.1, hp.2.1⟩
    have hCmono : Monotone C := by
      intro q q' hqq' a ha
      exact ha.imp (hqq' _ _) (hqq' _ _)
    have hCdir : DirectedOn (· ⊆ ·) (C '' d) := hd.mono_comp hCmono
    have hpc : p ⊆ ⋃₀ (C '' d) := by
      rintro ⟨a, b⟩ ⟨ha, hb, hne⟩
      rcases htchain ha hb hne with hab | hba
      · obtain ⟨q, hq, hab⟩ := (binary_relation_sSup_iff d).mp hab
        exact Set.mem_sUnion.mpr ⟨C q, ⟨q, hq, rfl⟩, Or.inl hab⟩
      · obtain ⟨q, hq, hba⟩ := (binary_relation_sSup_iff d).mp hba
        exact Set.mem_sUnion.mpr ⟨C q, ⟨q, hq, rfl⟩, Or.inr hba⟩
    obtain ⟨_, ⟨q, hq, rfl⟩, hpq⟩ :=
      DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
        (hdne.image C) hCdir hpfin hpc
    have htq : IsChain q t := by
      intro a ha b hb hne
      exact hpq (show (a, b) ∈ p from ⟨ha, hb, hne⟩)
    calc
      (n : ENat) = t.encard := hcard.symm
      _ ≤ s.chainHeight q := Set.encard_le_chainHeight_of_isChain s t hts htq
      _ ≤ sSup ((fun r : α → α → Prop ↦ s.chainHeight r) '' d) :=
        le_sSup ⟨q, hq, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨q, hq, rfl⟩
    exact hmono (le_sSup hq)

/-- The chain height of a directed pointwise supremum of relations is the join of the
false-relation height and the supremum of the members' heights. The index may be any sort,
including an empty one; no order or relation laws on the carrier are required. -/
theorem chainHeight_iSup_of_directed
    {α : Type u} {ι : Sort v}
    (s : Set α) (r : ι → α → α → Prop) (hr : Directed (· ≤ ·) r) :
    s.chainHeight (⨆ i, r i) =
      s.chainHeight (⊥ : α → α → Prop) ⊔ ⨆ i, s.chainHeight (r i) := by
  classical
  by_cases hi : Nonempty ι
  · obtain ⟨i⟩ := hi
    have heq : s.chainHeight (⨆ i, r i) = ⨆ i, s.chainHeight (r i) := by
      simpa only [← Set.range_comp, sSup_range, Function.comp_def] using
        (scottContinuous_chainHeight s).map_sSup
          (show (Set.range r).Nonempty from ⟨r i, ⟨i, rfl⟩⟩) hr.directedOn_range
    have hbot : s.chainHeight (⊥ : α → α → Prop) ≤ ⨆ i, s.chainHeight (r i) :=
      ((scottContinuous_chainHeight s).monotone
        (show (⊥ : α → α → Prop) ≤ r i from bot_le)).trans
          (le_iSup (fun i ↦ s.chainHeight (r i)) i)
    exact heq.trans (sup_eq_right.mpr hbot).symm
  · have : IsEmpty ι := ⟨fun i ↦ hi ⟨i⟩⟩
    simp only [iSup_of_empty, sup_bot_eq]

/-- The chain height of a union is the supremum of the heights of its pieces when points
in opposite exclusive pieces cannot compare. Quantification over all ordered pairs of pieces
excludes both comparison directions. The relation is arbitrary, and the index may be empty. -/
theorem chainHeight_iUnion_of_not_rel
    {α : Type u} {ι : Sort v}
    (s : ι → Set α) (r : α → α → Prop)
    (h : ∀ i j, ∀ a ∈ s i \ s j, ∀ b ∈ s j \ s i, ¬ r a b) :
    (⋃ i, s i).chainHeight r = ⨆ i, (s i).chainHeight r := by
  classical
  apply le_antisymm
  · rw [Set.chainHeight_eq_iSup]
    refine iSup_le fun c ↦ ?_
    have hdir : Directed (· ⊆ ·) (fun i ↦ c.1 ∩ s i) := by
      intro i j
      by_cases hij : c.1 ∩ s i ⊆ c.1 ∩ s j
      · exact ⟨j, hij, Set.Subset.rfl⟩
      · refine ⟨i, Set.Subset.rfl, ?_⟩
        by_contra hji
        obtain ⟨a, ha, haj⟩ := Set.not_subset.mp hij
        obtain ⟨b, hb, hbi⟩ := Set.not_subset.mp hji
        have hasj : a ∉ s j := fun hs ↦ haj ⟨ha.1, hs⟩
        have hbsi : b ∉ s i := fun hs ↦ hbi ⟨hb.1, hs⟩
        have hab : a ≠ b := fun hab ↦ hbsi (hab ▸ ha.2)
        exact (c.2.2 ha.1 hb.1 hab).elim
          (h i j a ⟨ha.2, hasj⟩ b ⟨hb.2, hbsi⟩)
          (h j i b ⟨hb.2, hbsi⟩ a ⟨ha.2, hasj⟩)
    have hcover : (⋃ i, c.1 ∩ s i) = c.1 := by
      rw [← Set.inter_iUnion, Set.inter_eq_left.mpr c.2.1]
    calc
      c.1.encard = c.1.chainHeight r := Set.encard_eq_chainHeight_of_isChain c.1 c.2.2
      _ = (⋃ i, c.1 ∩ s i).chainHeight r := congrArg (fun t ↦ t.chainHeight r) hcover.symm
      _ = ⨆ i, (c.1 ∩ s i).chainHeight r :=
        chainHeight_iUnion_of_directed (fun i ↦ c.1 ∩ s i) r hdir
      _ ≤ ⨆ i, (s i).chainHeight r :=
        iSup_mono fun i ↦ Set.chainHeight_mono r (c.1 ∩ s i) (s i) Set.inter_subset_right
  · refine iSup_le fun i ↦ ?_
    exact Set.chainHeight_mono r (s i) (⋃ i, s i) (Set.subset_iUnion s i)

/-- Chain height takes the maximum on a union when points in its two exclusive pieces
cannot compare across those pieces. Comparisons involving the intersection and all loops
are unrestricted. -/
theorem chainHeight_union_of_not_rel
    {α : Type u} (r : α → α → Prop) (s t : Set α)
    (h : ∀ a ∈ s \ t, ∀ b ∈ t \ s, ¬ r a b ∧ ¬ r b a) :
    (s ∪ t).chainHeight r = max (s.chainHeight r) (t.chainHeight r) := by
  simpa only [← Set.union_eq_iUnion, iSup_bool_eq, Bool.cond_true, Bool.cond_false] using
    chainHeight_iUnion_of_not_rel (fun b : Bool ↦ cond b s t) r (by
      intro i j a ha b hb
      cases i <;> cases j
      · exact (ha.2 ha.1).elim
      · exact (h b hb a ha).2
      · exact (h a ha b hb).1
      · exact (ha.2 ha.1).elim)

/-- The chain height of the union of the two tagged images under the disjoint sum relation
is the maximum of the factor chain heights. The relations are arbitrary, and either set or
ambient type may be empty. -/
theorem chainHeight_sum_liftRel
    {α : Type u} {β : Type v} (rα : α → α → Prop) (rβ : β → β → Prop)
    (s : Set α) (t : Set β) :
    ((Sum.inl : α → α ⊕ β) '' s ∪ (Sum.inr : β → α ⊕ β) '' t).chainHeight
        (Sum.LiftRel rα rβ) = max (s.chainHeight rα) (t.chainHeight rβ) := by
  calc
    _ = max (((Sum.inl : α → α ⊕ β) '' s).chainHeight (Sum.LiftRel rα rβ))
        (((Sum.inr : β → α ⊕ β) '' t).chainHeight (Sum.LiftRel rα rβ)) := by
      apply chainHeight_union_of_not_rel
      rintro _ ⟨⟨a, _, rfl⟩, _⟩ _ ⟨⟨b, _, rfl⟩, _⟩
      exact ⟨Sum.not_liftRel_inl_inr, Sum.not_liftRel_inr_inl⟩
    _ = _ := congrArg₂ max
      (Set.chainHeight_eq_of_relEmbedding s (RelEmbedding.sumLiftRelInl rα rβ))
      (Set.chainHeight_eq_of_relEmbedding t (RelEmbedding.sumLiftRelInr rα rβ))

/-- The chain height of the union of the two tagged images in the ordinary sum is the maximum
of the factor chain heights. The less-than relation is induced by `Sum.instLTSum` from the given
less-than structures on the factors; no relation laws or nonemptiness are required. -/
theorem chainHeight_sum
    {α : Type u} {β : Type v} [LT α] [LT β] (s : Set α) (t : Set β) :
    ((Sum.inl : α → α ⊕ β) '' s ∪ (Sum.inr : β → α ⊕ β) '' t).chainHeight
        (fun x y : α ⊕ β => x < y) =
      max (s.chainHeight (fun x y : α => x < y))
        (t.chainHeight (fun x y : β => x < y)) := by
  simpa only [Sum.lt_def] using
    chainHeight_sum_liftRel (fun x y : α => x < y) (fun x y : β => x < y) s t

end Set
