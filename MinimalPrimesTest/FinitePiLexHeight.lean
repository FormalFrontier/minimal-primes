/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.KrullDimension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# A dependent finite lexicographic product

The fibres over the two ordered indices are `Fin 2` and `Fin 3`. Applying the canonical
`toLex` image-height formula gives height six, rather than the height nine of the constant
`Fin 3` family. The dimension formula gives dimension five for the same heterogeneous family.
-/

private theorem chainHeight_univ_fin (n : ℕ) :
    (Set.univ : Set (Fin n)).chainHeight (fun x y : Fin n => x < y) = n := by
  rw [← Set.encard_eq_chainHeight_of_isChain _
    (isChain_of_trichotomous (r := fun x y : Fin n => x < y) Set.univ)]
  simp

example :
    ((toLex : (∀ i : Fin 2, Fin (i.val + 2)) → Lex (∀ i : Fin 2, Fin (i.val + 2))) ''
      Set.univ).chainHeight (fun x y : Lex (∀ i : Fin 2, Fin (i.val + 2)) => x < y) = 6 := by
  calc
    _ = ∏ i : Fin 2, (Set.univ : Set (Fin (i.val + 2))).chainHeight
        (fun x y : Fin (i.val + 2) => x < y) := by
      simpa only [Set.pi_univ] using
        Set.chainHeight_toLex_pi (fun i : Fin 2 => (Set.univ : Set (Fin (i.val + 2))))
          (by intro f _ i _ _ _; exact lt_irrefl (f i))
    _ = 6 := by
      simp only [Fin.prod_univ_two, chainHeight_univ_fin]
      norm_num

example :
    Order.krullDim
      ((toLex : (∀ i : Fin 2, Fin (i.val + 2)) → Lex (∀ i : Fin 2, Fin (i.val + 2))) ''
        Set.pi Set.univ (fun i : Fin 2 => (Set.univ : Set (Fin (i.val + 2))))) = 5 := by
  have hdim (n : ℕ) :
      Order.krullDim (Set.univ : Set (Fin (n + 1))) = ((n : ℕ∞) : WithBot ℕ∞) := by
    have hheight : (Set.univ : Set (Fin (n + 1))).chainHeight
        (fun x y : Fin (n + 1) => x < y) = (n + 1 : ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_one] using chainHeight_univ_fin (n + 1)
    exact le_antisymm
      ((Order.krullDim_le_iff_chainHeight_le _ n).mpr hheight.le)
      ((Order.le_krullDim_iff_le_chainHeight _ n).mpr hheight.ge)
  rw [Order.krullDim_toLex_pi, Fin.prod_univ_two, hdim 1, hdim 2]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  have hprod :
      (((1 : ℕ∞) : WithBot ℕ∞) + 1) * (((2 : ℕ∞) : WithBot ℕ∞) + 1) =
        ((6 : ℕ∞) : WithBot ℕ∞) := by
    norm_num [WithBot.coe_one, WithBot.coe_ofNat]
  rw [hprod, WithBot.map_coe]
  have hnat : (6 : ℕ) - 1 = 5 := by decide
  simpa only [hnat, Nat.cast_one, Nat.cast_ofNat, WithBot.coe_ofNat] using
    congrArg (fun h : ℕ∞ => (h : WithBot ℕ∞)) (ENat.natCast_sub 6 1).symm
