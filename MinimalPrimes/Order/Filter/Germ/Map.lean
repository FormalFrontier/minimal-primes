/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Filter.Germ.Basic

/-!
# Injectivity of varying application on germs

A family of functions acts on Mathlib's existing germs by `Filter.Germ.map₂` specialized
to evaluation. This action is injective exactly when the functions are eventually
injective. The filter and all three universes are arbitrary; in particular, neither
properness nor an inhabitant of the domain is required.

## References

The carrier, quotient induction, evaluation and eventual-equality interfaces are
Mathlib's filter-germ API, formalized by Yury Kudryashov and Abhimanyu Pallavi Sudhir.
-/

@[expose] public section

universe u v w

namespace Filter.Germ

variable {ι : Type u} {A : Type v} {B : Type w}

/-- Varying pointwise application on germs is injective exactly when the functions are
injective eventually. This includes empty types and the improper filter. -/
theorem injective_map₂_apply_coe_iff (D : Filter ι) (F : ι → A → B) :
    Function.Injective
      (map₂ (fun (φ : A → B) (a : A) => φ a) (F : Germ D (A → B))) ↔
      ∀ᶠ i in D, Function.Injective (F i) := by
  classical
  constructor
  · intro h
    by_cases hA : Nonempty A
    · -- Choose a collision at every bad fibre, and an equal pair at every good fibre.
      have hpair (i : ι) : ∃ a b : A, F i a = F i b ∧
          (a = b → Function.Injective (F i)) := by
        by_cases hi : Function.Injective (F i)
        · exact ⟨Classical.choice hA, Classical.choice hA, rfl, fun _ => hi⟩
        · obtain ⟨a, b, hab, hne⟩ : ∃ a b : A, F i a = F i b ∧ a ≠ b := by
            simpa only [Function.Injective, not_forall, exists_prop] using hi
          exact ⟨a, b, hab, fun heq => (hne heq).elim⟩
      choose a b hab hinj using hpair
      have heq : (a : Germ D A) = b := h (by
        simpa only [map₂_coe, coe_eq, Filter.EventuallyEq] using Eventually.of_forall hab)
      exact (coe_eq.mp heq).mono fun i hi => hinj i hi
    · exact Eventually.of_forall fun _ a _ _ => (hA ⟨a⟩).elim
  · intro h x y
    refine inductionOn₂ x y ?_
    intro a b hab
    apply coe_eq.mpr
    have heq : ∀ᶠ i in D, F i (a i) = F i (b i) := by
      simpa only [map₂_coe, coe_eq, Filter.EventuallyEq] using hab
    exact (h.and heq).mono fun _ hi => hi.1 hi.2

end Filter.Germ
