/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.Filter.Product.Reduced
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Data.ZMod.Basic

/-!
# A nilpotent section with nonadditive fibres

The index type is infinite, but the principal filter retains just two indices.
The zeroth fibre contains a nonzero square-zero value; the other fibres are
free monoids with zero and need no addition. The section has a common vanishing
power and represents a nonzero nilpotent element of the quotient.
-/

private def Fibre : ℕ → Type
  | 0 => ZMod 4
  | n + 1 => WithZero (FreeMonoid (Fin (n + 2)))

private instance (i : ℕ) : MonoidWithZero (Fibre i) := by
  cases i <;> dsimp only [Fibre] <;> infer_instance

private def sample : ∀ i, Fibre i
  | 0 => (2 : ZMod 4)
  | _ + 1 => 0

private theorem sample_eventually_nilpotent :
    ∀ᶠ i in Filter.principal ({0, 1} : Set ℕ), IsNilpotent (sample i) := by
  rw [Filter.eventually_principal]
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl
  · refine ⟨2, ?_⟩
    change (2 : ZMod 4) ^ 2 = 0
    decide
  · exact IsNilpotent.zero

example : sample 0 ≠ 0 ∧ ∃ n : ℕ, ∀ i ∈ ({0, 1} : Set ℕ), sample i ^ n = 0 := by
  constructor
  · change (2 : ZMod 4) ≠ 0
    decide
  · simpa only [Filter.eventually_principal] using
      sample_eventually_nilpotent.exists_pow_eq_zero_of_finite_mem
        (by simp : ({0, 1} : Set ℕ).Finite) (by simp)

example :
    (sample : (Filter.principal ({0, 1} : Set ℕ)).Product Fibre) ≠
        (0 : (Filter.principal ({0, 1} : Set ℕ)).Product Fibre) ∧
      @IsNilpotent ((Filter.principal ({0, 1} : Set ℕ)).Product Fibre) _ _
        (sample : (Filter.principal ({0, 1} : Set ℕ)).Product Fibre) := by
  constructor
  · intro hz
    have he := (Filter.Product.coe_eq (F := Filter.principal ({0, 1} : Set ℕ)) sample 0).1
      (hz.trans Filter.Product.coe_zero.symm)
    have hzero := (Filter.eventually_principal.1 he) 0 (by simp)
    change (2 : ZMod 4) = 0 at hzero
    exact (by decide : (2 : ZMod 4) ≠ 0) hzero
  · exact (Filter.Product.isNilpotent_coe_principal_iff sample (by simp)).2
      (Filter.eventually_principal.1 sample_eventually_nilpotent)
