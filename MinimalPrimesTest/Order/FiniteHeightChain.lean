/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.FiniteHeightChain
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.OrderIsoNat

/-!
# Finite-initial-height boundaries for antitone chains

The disjoint sum `ℕ ⊕ ℤ` has infinite Krull dimension and a non-well-founded strict order. Its
left component nevertheless contains elements of finite height. A chain starting at the left
value `1`, waiting for an arbitrary number of steps, then dropping to `0` tests the initial-height
hypothesis without imposing a global dimension or well-foundedness assumption.

A delayed drop also shows that equality at two adjacent indices does not make the chain
constant from either of those indices onward. This does not contradict eventual constancy.
-/

@[expose] public section

namespace FiniteHeightChainExamples

private theorem height_inl_nat (n : ℕ) : Order.height (Sum.inl n : ℕ ⊕ ℤ) = n := by
  have h := Order.height_eq_of_strictMono
    (fun k : ℕ => (Sum.inl k : ℕ ⊕ ℤ))
    (fun _ _ h => Sum.inl_lt_inl_iff.mpr h)
    (by
      intro a b h
      cases b with
      | inl b => exact ⟨b, Sum.inl_lt_inl_iff.mp h, rfl⟩
      | inr b => exact (Sum.not_inr_lt_inl h).elim) n
  simpa only [Order.height_nat] using h.symm

private def delayedDrop (d n : ℕ) : ℕ ⊕ ℤ := Sum.inl (if n ≤ d then 1 else 0)

private theorem delayedDrop_antitone (d : ℕ) : Antitone (delayedDrop d) := by
  intro i j hij
  simp only [delayedDrop, Sum.inl_le_inl_iff]
  split_ifs <;> omega

private theorem delayedDrop_initial_height (d : ℕ) :
    Order.height (delayedDrop d 0) = 1 := by
  simpa [delayedDrop] using height_inl_nat 1

/-- The disjoint sum `ℕ ⊕ ℤ` has infinite Krull dimension, even though its left component
contains elements of finite height. -/
theorem ambient_krullDim_eq_top : Order.krullDim (ℕ ⊕ ℤ) = ⊤ := by
  apply top_unique
  simpa only [Order.krullDim_nat] using
    Order.krullDim_le_of_strictMono (fun n : ℕ => (Sum.inl n : ℕ ⊕ ℤ))
      (fun _ _ h => Sum.inl_lt_inl_iff.mpr h)

-- The ambient strict order is not well-founded, as witnessed by `0, -1, -2, ...` on the right.
private theorem ambient_not_wellFoundedLT : ¬ WellFoundedLT (ℕ ⊕ ℤ) := by
  intro h
  let := h
  apply not_strictAnti_of_wellFoundedLT (fun n : ℕ => (Sum.inr (-(n : ℤ)) : ℕ ⊕ ℤ))
  intro i j hij
  apply Sum.inr_lt_inr_iff.mpr
  omega

-- This uses the lower-interval theorem with an independently computed initial height.
private theorem delayedDrop_eventually_eq (d : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → delayedDrop d n = delayedDrop d N := by
  let g : ℕ → Set.Iic (delayedDrop d 0) :=
    fun n => ⟨delayedDrop d n, delayedDrop_antitone d (Nat.zero_le n)⟩
  let : WellFoundedLT (Set.Iic (delayedDrop d 0)) :=
    Order.wellFoundedLT_Iic_of_height_lt_top _
      (by rw [delayedDrop_initial_height]; exact ENat.natCast_lt_top 1)
  have hg : Antitone g := fun _ _ h => delayedDrop_antitone d h
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hg
  exact ⟨N, fun n hn => congrArg Subtype.val (hN n hn).symm⟩

-- There is a genuine drop, however long the initial plateau lasts.
private theorem delayedDrop_ne_initial (d : ℕ) : delayedDrop d (d + 1) ≠ delayedDrop d 0 := by
  have h : ¬ d + 1 ≤ d := by omega
  simp [delayedDrop, h]

-- One adjacent equality cannot certify constancy from that index onward.
private theorem delayedDrop_adjacent_eq_then_ne :
    delayedDrop 1 0 = delayedDrop 1 1 ∧ delayedDrop 1 2 ≠ delayedDrop 1 1 := by
  simp [delayedDrop]

end FiniteHeightChainExamples
