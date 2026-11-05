/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

Portions adapted from Mathlib.Order.PiLex:
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Order.PiLex

/-!
# Lexicographic orders from strict fibre relations

A linearly ordered index and strict less-than relations on the fibres give a strict
lexicographic relation on the dependent function type. The index and fibre universes are
independent. The less-than relation is the one already supplied on `Lex (∀ i, β i)` by
`Mathlib.Order.PiLex`; no fibre weak order is required.

The associated partial order compares functions by equality or strict lexicographic comparison.
Prefixes in `Pi.Lex` use equality of fibre elements, not equivalence in a fibre preorder.
In particular, for a singleton index, distinct equivalent fibre elements need not remain weakly
comparable in this partial order. The construction does not assert an order isomorphism with
the given fibre preorder.

## References

The constructions generalize Chris Hughes's strict-order and partial-order formalizations in
`Mathlib.Order.PiLex`. The partial-order record is supplied by `partialOrderOfSO` from
`Mathlib.Order.RelClasses` (Jeremy Avigad, Mario Carneiro and Yury Kudryashov).
-/

@[expose] public section

universe u v

namespace Pi

variable {ι : Type u} {β : ι → Type v}

section StrictOrder

variable [LinearOrder ι] [∀ i, LT (β i)]

/-- The lexicographic less-than relation is strict whenever the given fibre less-than
relations are strict. This generalizes `Pi.Lex.isStrictOrder`. -/
instance (priority := 100) Lex.isStrictOrderOfLT [∀ i, IsStrictOrder (β i) (· < ·)] :
    IsStrictOrder (Lex (∀ i, β i)) (· < ·) := by
  refine { irrefl := ?_, trans := ?_ }
  · rintro f ⟨i, _, hi⟩
    exact irrefl (f i) hi
  · rintro f g h ⟨i, hfg, hfg'⟩ ⟨j, hgh, hgh'⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · refine ⟨i, fun k hk => (hfg k hk).trans (hgh k (lt_trans hk hij)), ?_⟩
      exact hgh i hij ▸ hfg'
    · exact ⟨i, fun k hk => (hfg k hk).trans (hgh k hk), _root_.trans hfg' hgh'⟩
    · refine ⟨j, fun k hk => (hfg k (lt_trans hk hji)).trans (hgh k hk), ?_⟩
      exact (hfg j hji).symm ▸ hgh'

/-- The partial order given by equality or strict lexicographic comparison, constructed by
`partialOrderOfSO` from the given fibre less-than relations.

The strict comparison uses equality of prefixes, not equivalence in a fibre preorder.
Even for a singleton index, the resulting weak order need not preserve weak comparisons
between distinct equivalent fibre elements. -/
instance (priority := 100) Lex.partialOrderOfLT [∀ i, IsStrictOrder (β i) (· < ·)] :
    PartialOrder (Lex (∀ i, β i)) :=
  @partialOrderOfSO (Lex (∀ i, β i)) (· < ·)
    (Lex.isStrictOrderOfLT (ι := ι) (β := β))

variable [∀ i, IsStrictOrder (β i) (· < ·)]

/-- The stored strict relation of the partial order is `Pi.Lex` on all functions, using
the given index and fibre less-than relations. -/
theorem Lex.partialOrderOfLT_lt :
    (Lex.partialOrderOfLT (ι := ι) (β := β)).lt =
      fun f g : Lex (∀ i, β i) =>
        Pi.Lex (fun i j : ι => i < j) (fun {i} (a b : β i) => a < b)
          (ofLex f) (ofLex g) := rfl

/-- The stored weak relation is equality or the same strict lexicographic relation. -/
theorem Lex.partialOrderOfLT_le_iff (f g : Lex (∀ i, β i)) :
    (Lex.partialOrderOfLT (ι := ι) (β := β)).le f g ↔ f = g ∨ f < g := Iff.rfl

end StrictOrder

/-- With fibre partial orders, the generalized construction agrees as a whole partial-order
record with the partial order supplied by `Mathlib.Order.PiLex`. -/
theorem Lex.partialOrderOfLT_eq [LinearOrder ι] [∀ i, PartialOrder (β i)] :
    Lex.partialOrderOfLT (ι := ι) (β := β) =
      (inferInstance : PartialOrder (Lex (∀ i, β i))) := by
  rfl

end Pi
