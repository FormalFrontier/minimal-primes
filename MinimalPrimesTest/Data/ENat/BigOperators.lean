/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Data.ENat.BigOperators

/-!
# Boundary cases of finite product expansions

The first three checks use the stock finite-set and scalar operations directly.
The finite numerical case also uses the public successor identity.
-/

open scoped BigOperators

universe u

-- The empty index set has zero nonempty-subset sum and empty product one.
private theorem empty_index {ι : Type u} (d : ι → WithBot ℕ∞) :
    WithBot.succ (∑ U ∈ (∅ : Finset ι).powerset with U.Nonempty, ∏ i ∈ U, d i) =
      ∏ i ∈ (∅ : Finset ι), WithBot.succ (d i) := by
  have h : ((∅ : Finset ι).powerset.filter Finset.Nonempty) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro U hU
    have hU0 : U = ∅ := Finset.subset_empty.mp (Finset.mem_powerset.mp hU)
    subst U
    exact Finset.not_nonempty_empty
  rw [h, Finset.sum_empty, Finset.prod_empty]
  decide

-- A singleton keeps the arbitrary scalar, with no nonbottom or finite premise.
private theorem arbitrary_singleton (a : WithBot ℕ∞) :
    WithBot.succ (∑ U ∈ ({0} : Finset ℕ).powerset with U.Nonempty,
      ∏ _i ∈ U, a) = ∏ _i ∈ ({0} : Finset ℕ), WithBot.succ a := by
  have h : ({0} : Finset ℕ).powerset.filter Finset.Nonempty = {{0}} := by decide
  rw [h, Finset.sum_singleton, Finset.prod_singleton, Finset.prod_singleton]

-- Bottom absorbs the sum even in the presence of a top value.
private theorem bottom_top :
    WithBot.succ (∑ U ∈ ({0, 1} : Finset ℕ).powerset with U.Nonempty,
      ∏ i ∈ U, if i = 0 then (⊥ : WithBot ℕ∞) else ⊤) =
      ∏ i ∈ ({0, 1} : Finset ℕ),
        WithBot.succ (if i = 0 then (⊥ : WithBot ℕ∞) else ⊤) := by
  decide

-- The three nonempty-subset terms are 2, 3 and 6, giving successor 12.
private theorem finite_values :
    WithBot.succ (∑ U ∈ ({0, 1} : Finset ℕ).powerset with U.Nonempty,
      ∏ i ∈ U, if i = 0 then (2 : WithBot ℕ∞) else 3) = (12 : ℕ∞) ∧
      (∏ i ∈ ({0, 1} : Finset ℕ),
        WithBot.succ (if i = 0 then (2 : WithBot ℕ∞) else 3)) = 12 := by
  constructor
  · rw [ENat.WithBot.succ_sum_powerset_nonempty]
    decide
  · decide
