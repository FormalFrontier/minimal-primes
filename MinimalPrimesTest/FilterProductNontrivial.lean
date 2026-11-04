/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product

/-!
# Varying fibres at a pure filter

A subsingleton fibre off the pure point supplies a default, while a Boolean fibre
at that point makes the product nontrivial. Replacing the default fibre by an
empty type leaves frequent nontriviality unchanged but destroys all total
sections. These two clients distinguish the two conjuncts of the criterion.
-/

@[expose] public section

namespace Filter.Product

/-- A trivial default fibre does not prevent a nontrivial product at the other,
Boolean fibre. No algebraic structure or fibrewise nontriviality is assumed. -/
theorem pure_true_nontrivial_with_default :
    Nontrivial ((pure true : Filter Bool).Product
      (fun b : Bool => if b then Bool else PUnit)) := by
  apply nontrivial_iff.mpr
  constructor
  · refine ⟨fun b => ?_⟩
    cases b
    · exact PUnit.unit
    · exact false
  · simpa using (inferInstance : Nontrivial Bool)

/-- Frequent nontriviality is insufficient when an empty fibre off the pure point
prevents a total section. This is the essential boundary of the criterion. -/
theorem pure_true_empty_off_support :
    (∃ᶠ b in pure true, Nontrivial (if b then Bool else Empty)) ∧
      ¬Nontrivial ((pure true : Filter Bool).Product
        (fun b : Bool => if b then Bool else Empty)) := by
  constructor
  · simpa using (inferInstance : Nontrivial Bool)
  · intro h
    obtain ⟨⟨s⟩, _⟩ := nontrivial_iff.mp h
    exact Empty.elim (s false)

end Filter.Product
