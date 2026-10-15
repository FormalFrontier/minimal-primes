/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import MinimalPrimes.RingTheory.KrullDimension.Integral

/-!
# Integral injections and dimension boundaries

The diagonal on `ZMod 4` is integral, injective, and not surjective; both
rings have nonzero nilpotents. The zero ring has dimension bottom. Independent
universe lifts preserve dimension, and the countable polynomial ring has
infinite dimension. The dimension equality for the proper diagonal uses the
public integral-homomorphism theorem; the other model proofs use Mathlib.

Mathlib supplies `IsIntegral.pair` (the product of monic witnesses),
`ULift.ringEquiv`, and the polynomial dimension formula.
-/

universe u v

namespace IntegralDimensionExamples

private def diagonal : ZMod 4 →+* ZMod 4 × ZMod 4 :=
  (RingHom.id (ZMod 4)).prod (RingHom.id (ZMod 4))

private theorem diagonal_injective : Function.Injective diagonal := by
  intro a b h
  exact congrArg Prod.fst h

private theorem diagonal_integral : diagonal.IsIntegral := by
  intro x
  change IsIntegral (ZMod 4) x
  exact IsIntegral.pair (isIntegral_algebraMap (x := x.1))
    (isIntegral_algebraMap (x := x.2))

private theorem diagonal_not_surjective : ¬ Function.Surjective diagonal := by
  intro h
  obtain ⟨x, hx⟩ := h (0, 1)
  have hzero : x = 0 := congrArg Prod.fst hx
  have hone : x = 1 := congrArg Prod.snd hx
  exact (by decide : (0 : ZMod 4) ≠ 1) (hzero.symm.trans hone)

private theorem source_nontrivial : Nontrivial (ZMod 4) :=
  ⟨⟨(0 : ZMod 4), 1, by decide⟩⟩

private theorem target_nontrivial : Nontrivial (ZMod 4 × ZMod 4) :=
  ⟨⟨((0, 0) : ZMod 4 × ZMod 4), (1, 1), by decide⟩⟩

private theorem two_ne_zero : (2 : ZMod 4) ≠ 0 := by decide

private theorem two_sq_zero : (2 : ZMod 4) ^ 2 = 0 := by decide

private theorem pair_ne_zero : ((2, 0) : ZMod 4 × ZMod 4) ≠ 0 := by decide

private theorem pair_sq_zero : ((2, 0) : ZMod 4 × ZMod 4) ^ 2 = 0 := by decide

private theorem zero_dimension : ringKrullDim (ZMod 1) = ⊥ :=
  ringKrullDim_eq_bot_of_subsingleton

private theorem zero_identity_injective :
    Function.Injective (RingHom.id (ZMod 1)) := Function.injective_id

private theorem zero_identity_integral : (RingHom.id (ZMod 1)).IsIntegral := by
  intro x
  exact (RingHom.id (ZMod 1)).isIntegralElem_map

private def crossUniverseEquiv : ULift.{u} (ZMod 4) ≃+* ULift.{v} (ZMod 4) :=
  ULift.ringEquiv.trans ULift.ringEquiv.symm

private theorem crossUniverse_injective :
    Function.Injective crossUniverseEquiv.{u, v}.toRingHom :=
  crossUniverseEquiv.injective

private theorem crossUniverse_integral :
    crossUniverseEquiv.{u, v}.toRingHom.IsIntegral := by
  intro x
  obtain ⟨r, rfl⟩ := crossUniverseEquiv.{u, v}.surjective x
  exact crossUniverseEquiv.toRingHom.isIntegralElem_map

private theorem crossUniverse_dimension :
    ringKrullDim (ULift.{u} (ZMod 4)) = ringKrullDim (ULift.{v} (ZMod 4)) :=
  ringKrullDim_eq_of_ringEquiv crossUniverseEquiv

private theorem infinite_dimension : ringKrullDim (MvPolynomial ℕ ℚ) = ⊤ := by
  simp

private theorem infinite_identity_injective :
    Function.Injective (RingHom.id (MvPolynomial ℕ ℚ)) := Function.injective_id

private theorem infinite_identity_integral :
    (RingHom.id (MvPolynomial ℕ ℚ)).IsIntegral := by
  intro x
  exact (RingHom.id (MvPolynomial ℕ ℚ)).isIntegralElem_map

end IntegralDimensionExamples

@[expose] public section

namespace MinimalPrimesTest.IntegralDimension

/-- The diagonal on the nonreduced ring `ZMod 4` is an integral injection
that is not surjective. -/
theorem diagonal_injective_integral_not_surjective :
    Function.Injective ((RingHom.id (ZMod 4)).prod (RingHom.id (ZMod 4))) ∧
      ((RingHom.id (ZMod 4)).prod (RingHom.id (ZMod 4))).IsIntegral ∧
      ¬ Function.Surjective ((RingHom.id (ZMod 4)).prod (RingHom.id (ZMod 4))) :=
  ⟨IntegralDimensionExamples.diagonal_injective,
    IntegralDimensionExamples.diagonal_integral,
    IntegralDimensionExamples.diagonal_not_surjective⟩

/-- The proper integral diagonal on `ZMod 4` preserves dimension. -/
theorem diagonal_ringKrullDim :
    ringKrullDim (ZMod 4) = ringKrullDim (ZMod 4 × ZMod 4) :=
  IntegralDimensionExamples.diagonal_integral.ringKrullDim_eq
    IntegralDimensionExamples.diagonal_injective

end MinimalPrimesTest.IntegralDimension
