/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Basic

/-!
# An empty fibre outside a pure filter

An empty source fibre prevents total sections even when the filter ignores that
coordinate. Thus reflection of eventual equality can hold while eventual
coordinate injectivity fails.
-/

private def emptyFalseBool : Bool → Type
  | false => Empty
  | true => Bool

private def boolCollapse (b : Bool) (_ : emptyFalseBool b) : PUnit := PUnit.unit

private theorem empty_fibre_constant_map :
    IsEmpty (∀ b, emptyFalseBool b) ∧
      (∀ f g : ∀ b, emptyFalseBool b,
        (∀ᶠ b in (pure true : Filter Bool), boolCollapse b (f b) = boolCollapse b (g b)) →
          ∀ᶠ b in (pure true : Filter Bool), f b = g b) ∧
      ¬ ∀ᶠ b in (pure true : Filter Bool), Function.Injective (boolCollapse b) := by
  have hK : IsEmpty (∀ b, emptyFalseBool b) := ⟨fun f => Empty.elim (f false)⟩
  refine ⟨hK, ?_, ?_⟩
  · exact (Filter.forall_eventually_eq_of_map_eq_iff (pure true) boolCollapse).2 (Or.inl hK)
  · intro h
    have hi : Function.Injective (boolCollapse true) := Filter.mem_pure.mp h
    have hfalse : (false : Bool) = true := hi rfl
    cases hfalse
