/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Filter.Basic

/-!
# Quantifying over dependent sections eventually

A total section supplies fallback values when choosing a witness in each fibre.
Consequently, testing a predicate along every section detects whether it holds
for all elements of the fibres eventually. The fibres may belong to any sort.

The witness argument generalizes the diagonal argument for centers of filter germs.
-/

@[expose] public section

universe u v

namespace Filter

variable {ι : Type u} {R : ι → Sort v} {D : Filter ι} {P : ∀ i, R i → Prop}

/-- A predicate holds throughout the fibres eventually exactly when it holds
along every total section eventually. The supplied section provides fallback
values; no properness or separate inhabitance assumption is needed. -/
theorem eventually_forall_iff_forall_section (s : ∀ i, R i) :
    (∀ᶠ i in D, ∀ x : R i, P i x) ↔ ∀ f : ∀ i, R i, ∀ᶠ i in D, P i (f i) := by
  classical
  constructor
  · intro h f
    exact h.mono fun i hi => hi (f i)
  · intro h
    have hex (i : ι) : ∃ x : R i, P i x → ∀ y, P i y := by
      by_cases hi : ∀ x, P i x
      · exact ⟨s i, fun _ => hi⟩
      · obtain ⟨x, hx⟩ := not_forall.mp hi
        exact ⟨x, fun h => (hx h).elim⟩
    choose f hf using hex
    exact (h f).mono fun i hi => hf i hi

end Filter
