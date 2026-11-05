/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Order.SuccPred.WithBot

/-!
# Successors of finite product expansions

The successor of the sum of products over the nonempty subsets of a finite set
is the product of the successors. The scalar values lie in `WithBot ℕ∞`, so the
identity includes bottom and top, as well as the empty index set.

The proof reuses Mathlib's whole finite-product expansion `Finset.prod_add_one`;
the remaining steps separate the empty-subset term and handle the bottom value.
-/

@[expose] public section

open scoped BigOperators

universe u v

namespace ENat.WithBot

private theorem sum_powerset_nonempty_add_one {ι : Type u} {R : Type v} [CommSemiring R]
    (J : Finset ι) (e : ι → R) :
    (∑ U ∈ J.powerset with U.Nonempty, ∏ i ∈ U, e i) + 1 =
      ∑ U ∈ J.powerset, ∏ i ∈ U, e i := by
  classical
  have h : J.powerset.filter Finset.Nonempty = J.powerset.erase ∅ := by
    rw [← Finset.filter_ne']
    exact Finset.filter_congr (fun _ _ => Finset.nonempty_iff_ne_empty)
  rw [h]
  simpa only [Finset.prod_empty] using
    (Finset.sum_erase_add J.powerset (fun U => ∏ i ∈ U, e i) (Finset.empty_mem_powerset J))

/-- The successor of the nonempty-subset product expansion is the product of the
successors, including the empty index set and arbitrary bottom or top values. -/
theorem succ_sum_powerset_nonempty {ι : Type u} (J : Finset ι) (d : ι → WithBot ℕ∞) :
    WithBot.succ (∑ U ∈ J.powerset with U.Nonempty, ∏ i ∈ U, d i) =
      ∏ i ∈ J, WithBot.succ (d i) := by
  classical
  by_cases h : ∃ i ∈ J, d i = ⊥
  · obtain ⟨i, hi, hdi⟩ := h
    -- The singleton term detects bottom without any assertion about bottom times zero.
    have hs : (∑ U ∈ J.powerset with U.Nonempty, ∏ j ∈ U, d j) = ⊥ := by
      apply WithBot.sum_eq_bot_iff.mpr
      refine ⟨{i}, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simpa), by simp⟩
      · simpa using hdi
    rw [hs, WithBot.succ_bot]
    exact (Finset.prod_eq_zero hi (by simp [hdi])).symm
  · let e : ι → ℕ∞ := fun i => (d i).unbotD 0
    have he (i : ι) (hi : i ∈ J) : (e i : WithBot ℕ∞) = d i := by
      have hdi : d i ≠ ⊥ := fun heq => h ⟨i, hi, heq⟩
      cases hd : d i <;> simp_all [e]
    have hp (U : Finset ι) (hU : U ⊆ J) :
        ((∏ i ∈ U, e i : ℕ∞) : WithBot ℕ∞) = ∏ i ∈ U, d i := by
      calc
        _ = ∏ i ∈ U, (e i : WithBot ℕ∞) :=
          Finset.prod_hom_rel
            (r := fun (a : ℕ∞) (b : WithBot ℕ∞) => (a : WithBot ℕ∞) = b)
            (f := e) (g := fun i => (e i : WithBot ℕ∞)) (s := U)
            (by simp) (by intro a b c hbc; simp only [WithBot.coe_mul, hbc])
        _ = _ := Finset.prod_congr rfl (fun i hi => he i (hU hi))
    have hs : ((∑ U ∈ J.powerset with U.Nonempty, ∏ i ∈ U, e i : ℕ∞) :
        WithBot ℕ∞) = ∑ U ∈ J.powerset with U.Nonempty, ∏ i ∈ U, d i := by
      rw [WithBot.coe_sum]
      exact Finset.sum_congr rfl (fun U hU => hp U
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1))
    rw [← hs, WithBot.succ_coe, Order.succ_eq_add_one,
      sum_powerset_nonempty_add_one, ← Finset.prod_add_one]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← he i hi, WithBot.succ_coe, Order.succ_eq_add_one]

end ENat.WithBot
