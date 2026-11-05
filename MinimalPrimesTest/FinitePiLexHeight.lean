/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.ChainHeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# A dependent finite lexicographic product

The fibres over the two ordered indices are `Fin 2` and `Fin 3`. Applying the canonical
`toLex` image-height formula gives height six, rather than the height nine of the constant
`Fin 3` family.
-/

example :
    ((toLex : (∀ i : Fin 2, Fin (i.val + 2)) → Lex (∀ i : Fin 2, Fin (i.val + 2))) ''
      Set.univ).chainHeight (fun x y : Lex (∀ i : Fin 2, Fin (i.val + 2)) => x < y) = 6 := by
  have hheight (n : ℕ) :
      (Set.univ : Set (Fin n)).chainHeight (fun x y : Fin n => x < y) = n := by
    rw [← Set.encard_eq_chainHeight_of_isChain _
      (isChain_of_trichotomous (r := fun x y : Fin n => x < y) Set.univ)]
    simp
  calc
    _ = ∏ i : Fin 2, (Set.univ : Set (Fin (i.val + 2))).chainHeight
        (fun x y : Fin (i.val + 2) => x < y) := by
      simpa only [Set.pi_univ] using
        Set.chainHeight_toLex_pi (fun i : Fin 2 => (Set.univ : Set (Fin (i.val + 2))))
          (by intro f _ i _ _ _; exact lt_irrefl (f i))
    _ = 6 := by
      simp only [Fin.prod_univ_two, hheight]
      norm_num
