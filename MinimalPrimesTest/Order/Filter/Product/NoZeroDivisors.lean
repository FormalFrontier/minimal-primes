/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MinimalPrimes.Order.Filter.Germ.NoZeroDivisors
public import Mathlib.Algebra.Ring.Nat

/-!
# No zero divisors without absorption

The fibres have varying finite sizes, a distinguished zero and constant nonzero
multiplication. Their ultrafilter product has no zero divisors, although zero is
not absorbing. The constant-fibre germ criterion applies to the same weak data.
These operations admit no monoid-with-zero structure. In contrast,
complementary supports give zero divisors over the natural numbers at the proper
top filter on a two-point index type.
-/

@[expose] public section

open Filter

namespace FilterProductNoZeroDivisorsExamples

private def Nonabsorbing (n : ℕ) := Fin (n + 2)

private instance (n : ℕ) : Zero (Nonabsorbing n) :=
  ⟨(⟨0, Nat.zero_lt_succ (n + 1)⟩ : Fin (n + 2))⟩

private instance (n : ℕ) : Mul (Nonabsorbing n) :=
  ⟨fun _ _ => (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩ : Fin (n + 2))⟩

private theorem mul_ne_zero (n : ℕ) (a b : Nonabsorbing n) : a * b ≠ 0 := by
  intro h
  exact Nat.one_ne_zero (congrArg Fin.val h)

private theorem noZeroDivisors_fibre (n : ℕ) : NoZeroDivisors (Nonabsorbing n) :=
  ⟨fun {a b} h => (mul_ne_zero n a b h).elim⟩

-- Both criteria use precisely these Zero and Mul records, not an absorbing extension.
example (U : Ultrafilter ℕ) :
    @NoZeroDivisors ((U : Filter ℕ).Product Nonabsorbing)
        (Con.hasMul (productCon (U : Filter ℕ) Nonabsorbing))
        (Con.zero (productCon (U : Filter ℕ) Nonabsorbing)) ∧
      NoZeroDivisors (Germ (U : Filter ℕ) (Nonabsorbing 0)) ∧
        ∀ n : ℕ, (0 : Nonabsorbing n) * 0 ≠ 0 :=
  ⟨(Product.noZeroDivisors_iff_eventually U).2
      (Eventually.of_forall noZeroDivisors_fibre),
    (Germ.noZeroDivisors_iff U).2 (noZeroDivisors_fibre 0), fun n => mul_ne_zero n 0 0⟩

private def leftSupport : Bool → ℕ := fun b => if b then 0 else 1

private def rightSupport : Bool → ℕ := fun b => if b then 1 else 0

-- Properness cannot replace the ultrafilter hypothesis, even for domain fibres.
example : NeBot (⊤ : Filter Bool) ∧ NoZeroDivisors ℕ ∧
    ¬NoZeroDivisors ((⊤ : Filter Bool).Product (fun _ : Bool => ℕ)) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro h
  have hmul :
      ((· * ·) :
        (⊤ : Filter Bool).Product (fun _ : Bool => ℕ) →
        (⊤ : Filter Bool).Product (fun _ : Bool => ℕ) →
        (⊤ : Filter Bool).Product (fun _ : Bool => ℕ))
        (leftSupport : (⊤ : Filter Bool).Product (fun _ : Bool => ℕ))
        (rightSupport : (⊤ : Filter Bool).Product (fun _ : Bool => ℕ)) = 0 := by
    rw [← Product.coe_mul, ← Product.coe_zero]
    exact (Product.coe_eq (leftSupport * rightSupport) 0).2
      (Eventually.of_forall fun b => by cases b <;> rfl)
  rcases @NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
      ((⊤ : Filter Bool).Product (fun _ : Bool => ℕ))
      (inferInstance : Mul ((⊤ : Filter Bool).Product (fun _ : Bool => ℕ)))
      (inferInstance : Zero ((⊤ : Filter Bool).Product (fun _ : Bool => ℕ))) h
      (leftSupport : (⊤ : Filter Bool).Product (fun _ : Bool => ℕ))
      (rightSupport : (⊤ : Filter Bool).Product (fun _ : Bool => ℕ)) hmul with hl | hr
  · have he := (Product.coe_eq leftSupport 0).1 hl
    exact Nat.one_ne_zero (Filter.mem_top_iff_forall.1 he false)
  · have he := (Product.coe_eq rightSupport 0).1 hr
    exact Nat.one_ne_zero (Filter.mem_top_iff_forall.1 he true)

end FilterProductNoZeroDivisorsExamples
