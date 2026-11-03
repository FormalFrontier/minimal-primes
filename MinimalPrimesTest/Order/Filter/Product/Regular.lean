/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Product.Regular

/-!
# Regularity in varying left-projection magmas

On `Fin (n + 2)`, left-projection multiplication is right-cancellative but not
left-cancellative. The top-filter product preserves these distinctions and is
noncommutative. None of these fibre multiplications has a two-sided identity.
-/

@[expose] public section

open Filter

namespace FilterProductRegularExamples

private def LeftProjection (n : ℕ) := Fin (n + 2)

private instance (n : ℕ) : Mul (LeftProjection n) := ⟨fun x _ => x⟩

private def firstSection : ∀ n, LeftProjection n :=
  fun n => (⟨0, Nat.zero_lt_succ (n + 1)⟩ : Fin (n + 2))

private def secondSection : ∀ n, LeftProjection n :=
  fun n => (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩ : Fin (n + 2))

-- The same multiplication is used in the fibre criteria and the quotient computations.
example :
    let a : (⊤ : Filter ℕ).Product LeftProjection := firstSection
    let b : (⊤ : Filter ℕ).Product LeftProjection := secondSection
    IsRightRegular a ∧ ¬IsLeftRegular a ∧ a * b = a ∧ b * a = b ∧ a ≠ b := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Product.isRightRegular_coe_iff (⊤ : Filter ℕ) firstSection).2
      (Eventually.of_forall fun _ _ _ h => h)
  · intro h
    have h₀ := Filter.mem_top_iff_forall.1
      ((Product.isLeftRegular_coe_iff (⊤ : Filter ℕ) firstSection).1 h) 0
    have h01 : firstSection 0 = secondSection 0 := h₀ rfl
    exact Nat.zero_ne_one (congrArg Fin.val h01)
  · exact (Product.coe_mul (F := (⊤ : Filter ℕ)) firstSection secondSection).symm
  · exact (Product.coe_mul (F := (⊤ : Filter ℕ)) secondSection firstSection).symm
  · intro h
    have h₀ := Filter.mem_top_iff_forall.1
      ((Product.coe_eq (F := (⊤ : Filter ℕ)) firstSection secondSection).1 h) 0
    exact Nat.zero_ne_one (congrArg Fin.val h₀)

-- No two-sided identity can be added while retaining this multiplication.
example (n : ℕ) : ¬∃ e : LeftProjection n,
    (∀ x, e * x = x) ∧ ∀ x, x * e = x := by
  rintro ⟨e, he, _⟩
  have he_first : e = firstSection n := he (firstSection n)
  have he_second : e = secondSection n := he (secondSection n)
  have h01 : firstSection n = secondSection n := he_first.symm.trans he_second
  exact Nat.zero_ne_one (congrArg Fin.val h01)

end FilterProductRegularExamples
