/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Germ.Reduced
public import Mathlib.Data.ZMod.Basic

/-!
# Reduced and nonreduced germs

The bottom filter hides the nonzero square-zero element of `ZMod 4`, whereas
a pure-point filter detects it. Natural-number coefficients give a positive
case for arbitrary filters through the reducedness instance. A representative
that is one away from the retained point can still define a nilpotent germ.
-/

public section

namespace FilterGermExamples

/-- The same nonreduced coefficient ring gives reduced germs at bottom and
nonreduced germs at a pure-point filter. -/
theorem germ_zmod_four_bottom_and_pure :
    IsReduced (Filter.Germ (⊥ : Filter ℕ) (ZMod 4)) ∧
      ¬ IsReduced (Filter.Germ (pure (0 : ℕ)) (ZMod 4)) := by
  constructor
  · exact (Filter.Germ.isReduced_iff_eq_bot_or _).2 (Or.inl rfl)
  · -- Compute the coefficient identities before assuming reducedness.
    have hsq : (2 : ZMod 4) ^ 2 = 0 := by decide
    have hne : (2 : ZMod 4) ≠ 0 := by decide
    intro h
    let _ : IsReduced (ZMod 4) := (Filter.Germ.isReduced_iff _).1 h
    exact hne (eq_zero_of_pow_eq_zero (n := 2) hsq)

example (D : Filter ℕ) : IsReduced (Filter.Germ D ℕ) := inferInstance

example : IsNilpotent
    ((fun n : ℕ => if n = 0 then (2 : ZMod 4) else 1) :
      Filter.Germ (Filter.principal ({0} : Set ℕ)) (ZMod 4)) := by
  apply (Filter.Germ.isNilpotent_coe_iff_of_finite_mem _ _
    (by simp : ({0} : Set ℕ).Finite) (by simp)).2
  rw [Filter.eventually_principal]
  intro i hi
  have hi0 : i = 0 := Set.mem_singleton_iff.1 hi
  subst i
  exact ⟨2, by decide⟩

end FilterGermExamples
