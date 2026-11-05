/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.KrullDimension
import Mathlib.Order.Fin.Tuple

/-!
# Boundary cases for pointwise product ranks

Empty products have rank zero without inhabited fibres. In the pointwise square
of a two-element chain, the top has height two and the bottom has coheight two.
These calculations use the binary rank identities and the canonical two-coordinate
order isomorphism.
-/

universe u v

private theorem empty_ranks
    {ι : Type u} [IsEmpty ι] {β : ι → Type v} [∀ i, Preorder (β i)]
    (f : ∀ i, β i) : Order.height f = 0 ∧ Order.coheight f = 0 := by
  let : Fintype ι := Fintype.ofIsEmpty
  constructor
  · rw [Order.height_pi]
    exact Finset.sum_eq_zero fun i _ => isEmptyElim i
  · rw [Order.coheight_pi]
    exact Finset.sum_eq_zero fun i _ => isEmptyElim i

private theorem square_ranks :
    Order.height (fun _ : Fin 2 => (1 : Fin 2)) = 2 ∧
      Order.coheight (fun _ : Fin 2 => (0 : Fin 2)) = 2 := by
  have hheight : Order.height (1 : Fin 2) = 1 := by
    have h := Order.height_eq_of_strictMono
      (f := fun x : Fin 2 => (x : ℕ)) (fun _ _ h => h)
      (by
        intro a b h
        exact ⟨⟨b, lt_trans h a.isLt⟩, h, rfl⟩) (1 : Fin 2)
    simpa using h
  have hcoheight : Order.coheight (0 : Fin 2) = 1 := by
    calc
      Order.coheight (0 : Fin 2) = Order.height (OrderDual.toDual (0 : Fin 2)) :=
        (Order.height_toDual _).symm
      _ = Order.height (Fin.revOrderIso (OrderDual.toDual (0 : Fin 2))) :=
        (Order.height_orderIso Fin.revOrderIso _).symm
      _ = 1 := by simpa using hheight
  let e := OrderIso.piFinTwoIso (fun _ : Fin 2 => Fin 2)
  constructor
  · calc
      Order.height (fun _ : Fin 2 => (1 : Fin 2)) =
          Order.height (e (fun _ : Fin 2 => (1 : Fin 2))) :=
        (Order.height_orderIso e _).symm
      _ = Order.height (1 : Fin 2) + Order.height (1 : Fin 2) := by
        change Order.height ((1 : Fin 2), (1 : Fin 2)) = _
        exact Order.height_prod _ _
      _ = 2 := by rw [hheight]; rfl
  · calc
      Order.coheight (fun _ : Fin 2 => (0 : Fin 2)) =
          Order.coheight (e (fun _ : Fin 2 => (0 : Fin 2))) :=
        (Order.coheight_orderIso e _).symm
      _ = Order.coheight (0 : Fin 2) + Order.coheight (0 : Fin 2) := by
        change Order.coheight ((0 : Fin 2), (0 : Fin 2)) = _
        exact Order.coheight_prod _ _
      _ = 2 := by rw [hcoheight]; rfl
