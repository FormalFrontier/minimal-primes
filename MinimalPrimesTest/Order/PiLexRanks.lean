/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.KrullDimension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Point ranks in a finite lexicographic cube

The constant section with value one in `Fin 3 → Fin 3` has height and coheight
thirteen in the canonical equality-or-strict lexicographic partial order. The
suffix weights are nine, three and one. The same section has both ranks three
in the original pointwise preorder, as computed by the finite pointwise rank APIs.
-/

private theorem lex_middle_section_ranks :
    @Order.height (Lex (Fin 3 → Fin 3))
        (Pi.Lex.partialOrderOfLT (ι := Fin 3) (β := fun _ => Fin 3)).toPreorder
        (toLex (fun _ : Fin 3 => (1 : Fin 3))) = 13 ∧
      @Order.coheight (Lex (Fin 3 → Fin 3))
        (Pi.Lex.partialOrderOfLT (ι := Fin 3) (β := fun _ => Fin 3)).toPreorder
        (toLex (fun _ : Fin 3 => (1 : Fin 3))) = 13 ∧
      Order.height (fun _ : Fin 3 => (1 : Fin 3)) = 3 ∧
      Order.coheight (fun _ : Fin 3 => (1 : Fin 3)) = 3 := by
  have hwhole : (Set.univ : Set (Fin 3)).chainHeight (· < ·) = 3 := by
    rw [← Set.encard_eq_chainHeight_of_isChain _
      (isChain_of_trichotomous (r := fun x y : Fin 3 => x < y) Set.univ)]
    simp [ENat.card_eq_coe_fintype_card]
  have hheight : Order.height (1 : Fin 3) = 1 := by
    rw [Order.height_eq_chainHeight_Iio,
      show Set.Iio (1 : Fin 3) = {0} from Set.ext (by decide)]
    simp [← Set.encard_eq_chainHeight_of_isChain _ IsChain.singleton]
  have hcoheight : Order.coheight (1 : Fin 3) = 1 := by
    rw [Order.coheight_eq_chainHeight_Ioi,
      show Set.Ioi (1 : Fin 3) = {2} from Set.ext (by decide)]
    simp [← Set.encard_eq_chainHeight_of_isChain _ IsChain.singleton]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Order.height_toLex_pi]
    norm_num [hheight, hwhole, Fin.sum_univ_three, Finset.prod_filter, Fin.prod_univ_three]
    decide
  · rw [Order.coheight_toLex_pi]
    norm_num [hcoheight, hwhole, Fin.sum_univ_three, Finset.prod_filter, Fin.prod_univ_three]
    decide
  · rw [Order.height_pi]
    norm_num [hheight, Fin.sum_univ_three]
  · rw [Order.coheight_pi]
    norm_num [hcoheight, Fin.sum_univ_three]
