/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MinimalPrimes.Order.KrullDimension
import Mathlib.Data.Set.Sigma
import Mathlib.Tactic.NormNum

/-!
# Lexicographic dimension and point-rank clients

The family application uses the stock Sigma set. The sparse numerical example
has an infinite ambient index with an empty middle fiber excluded from the sum.
The middle point of `Fin 3 ×ₗ Fin 3` has height and coheight four, rather than the
pointwise values two: each first-coordinate step has weight three, the whole
second factor's strict-chain vertex height, not its dimension two.
-/

open scoped BigOperators

universe u v

private theorem krullDim_toLex_sigma_family
    {ι : Type u} {α : ι → Type v} [Preorder ι] [∀ i, Preorder (α i)]
    (s : ∀ i, Set (α i))
    (hI : (Sigma.fst '' (Set.univ.sigma s)).Finite)
    (hc : IsChain (· < ·) (Sigma.fst '' (Set.univ.sigma s))) :
    Order.krullDim ((toLex : (Σ i, α i) → (Σₗ i, α i)) '' (Set.univ.sigma s)) =
      Order.krullDim (Sigma.fst '' (Set.univ.sigma s)) +
        ∑ i ∈ hI.toFinset, Order.krullDim (s i) := by
  have hpre (i : ι) : (Sigma.mk i) ⁻¹' (Set.univ.sigma s) = s i :=
    Set.mk_preimage_sigma (s := Set.univ) (t := s) (i := i) (Set.mem_univ i)
  calc
    _ = Order.krullDim (Sigma.fst '' (Set.univ.sigma s)) +
        ∑ i ∈ hI.toFinset, Order.krullDim ((Sigma.mk i) ⁻¹' (Set.univ.sigma s)) :=
      Order.krullDim_toLex_sigma (Set.univ.sigma s) hI hc
    _ = _ := congrArg
      (fun d : WithBot ENat ↦ Order.krullDim (Sigma.fst '' (Set.univ.sigma s)) + d)
      (Finset.sum_congr rfl (fun i _ ↦
        congrArg (fun t : Set (α i) ↦ Order.krullDim t) (hpre i)))

private theorem krullDim_toLex_sigma_sparse :
    Order.krullDim ((toLex : (Σ _ : ℕ, Unit) → (Σₗ _ : ℕ, Unit)) ''
      ({⟨0, ()⟩, ⟨2, ()⟩} : Set (Σ _ : ℕ, Unit))) = 1 := by
  let S : Set (Σ _ : ℕ, Unit) := {⟨0, ()⟩, ⟨2, ()⟩}
  have himage : Sigma.fst '' S = ({0, 2} : Set ℕ) := by simp [S]
  have hI : (Sigma.fst '' S).Finite := by
    rw [himage]
    exact (Set.finite_singleton 2).insert 0
  have hc : IsChain (· < ·) (Sigma.fst '' S) :=
    fun _ _ _ _ h ↦ lt_or_gt_of_ne h
  have hheight : (Sigma.fst '' S).chainHeight (· < ·) = 2 := by
    rw [← Set.encard_eq_chainHeight_of_isChain _ hc, himage]
    exact Set.encard_pair (by decide)
  have hindex : Order.krullDim (Sigma.fst '' S) = 1 :=
    le_antisymm
      ((Order.krullDim_le_iff_chainHeight_le _ 1).mpr (by norm_num [hheight]))
      ((Order.le_krullDim_iff_le_chainHeight _ 1).mpr (by norm_num [hheight]))
  have hfiber (i : ℕ) (hi : i ∈ hI.toFinset) :
      Order.krullDim ((Sigma.mk i) ⁻¹' S) = 0 := by
    obtain ⟨⟨j, a⟩, ha, hji⟩ := hI.mem_toFinset.mp hi
    dsimp at hji
    subst j
    have : Nonempty ((Sigma.mk i) ⁻¹' S) := ⟨⟨a, ha⟩⟩
    exact Order.krullDim_eq_zero
  change Order.krullDim ((toLex : (Σ _ : ℕ, Unit) → (Σₗ _ : ℕ, Unit)) '' S) = 1
  rw [Order.krullDim_toLex_sigma S hI hc, hindex,
    Finset.sum_eq_zero hfiber, add_zero]

private theorem lex_middle_point_ranks :
    Order.height (toLex ((1 : Fin 3), (1 : Fin 3))) = 4 ∧
      Order.coheight (toLex ((1 : Fin 3), (1 : Fin 3))) = 4 := by
  have hwhole : (Set.univ : Set (Fin 3)).chainHeight (· < ·) = 3 := by
    rw [← Set.encard_eq_chainHeight_of_isChain _ (fun _ _ _ _ h ↦ lt_or_gt_of_ne h)]
    simp [ENat.card_eq_coe_fintype_card]
  have hheight : Order.height (1 : Fin 3) = 1 := by
    rw [Order.height_eq_chainHeight_Iio,
      show Set.Iio (1 : Fin 3) = {0} from Set.ext (by decide),
      ← Set.encard_eq_chainHeight_of_isChain _ IsChain.singleton, Set.encard_singleton]
  have hcoheight : Order.coheight (1 : Fin 3) = 1 := by
    rw [Order.coheight_eq_chainHeight_Ioi,
      show Set.Ioi (1 : Fin 3) = {2} from Set.ext (by decide),
      ← Set.encard_eq_chainHeight_of_isChain _ IsChain.singleton, Set.encard_singleton]
  norm_num [Order.height_toLex_prod, Order.coheight_toLex_prod, hwhole, hheight, hcoheight]
